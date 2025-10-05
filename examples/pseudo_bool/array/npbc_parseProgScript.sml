(*
  Add shared pbp parsing, normalization and other common stuff to npbc_arrayProg
*)
Theory npbc_parseProg
Ancestors
  npbc_check pb_parse npbc_arrayProg pbc_normalise mlint
Libs
  preamble basis

val _ = translation_extends"npbc_arrayProg";

val () = computeLib.set_skip computeLib.the_compset “COND” (SOME 1);

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

val r = translate strip_numbers_aux_def;
val strip_numbers_aux_side_def = theorem "strip_numbers_aux_side_def";
val strip_numbers_aux_side = Q.prove(
  `∀x y. strip_numbers_aux_side x y <=> T`,
  Induct>>rw[Once strip_numbers_aux_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate strip_numbers_def;

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

val r = translate apply_lit_def;
val r = translate parse_lit_num_def;

val r = translate parse_cutting_aux_def;
val parse_cutting_aux_side_def = theorem "parse_cutting_aux_side_def";
val parse_cutting_aux_side = Q.prove(
  `∀x y z. parse_cutting_aux_side x y z <=> T`,
  Induct_on`y`>>rw[Once parse_cutting_aux_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate parse_cutting_def;

val r = translate parse_var_def;

val r = translate parse_subst_aux_def;

val r = translate parse_subst_def;

val r = translate pbcTheory.lit_var_def;
val r = translate compact_lhs_def;
val r = translate term_le_def;
val r = translate mk_coeff_def;
val r = translate normalise_lhs_def;

val r = translate pbc_to_npbc_def;

val r = translate parse_constraint_LHS_aux_def;
val r = translate parse_constraint_LHS_def;

val r = translate pbcTheory.map_pbc_def;
val r = translate map_f_ns_def;
val r = translate parse_constraint_npbc_def;

val r = translate strip_rup_hint_aux_def;
val strip_rup_hint_aux_side_def = fetch "-" "strip_rup_hint_aux_side_def";
val strip_rup_hint_aux_side = Q.prove(
  `∀x y. strip_rup_hint_aux_side x y <=> T`,
  Induct>>rw[Once strip_rup_hint_aux_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate strip_rup_hint_def;
val r = translate parse_rup_hint_def;
val r = translate parse_rup_def;

val r = translate start_subproof_def;
val r = translate parse_red_header_def;
val r = translate parse_pbc_header_def;

val r = translate strip_term_def;
val r = translate tokenize_def;
val r = translate strip_term_line_aux_def;
val r = translate strip_term_line_def;

val r = translate colon_id_opt_def;
val colon_id_opt_side_def = fetch "-" "colon_id_opt_side_def";
val colon_id_opt_side = Q.prove(
  `∀x. colon_id_opt_side x <=> T`,
  rw[Once colon_id_opt_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate parse_lstep_aux_def;

val r = translate check_end_def;

val r = translate blanks_def;

(* TODO: Mostly copied from mlintTheory *)
val result = translate (fromChar_unsafe_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def]);

Definition fromChars_range_unsafe_tail_def:
  fromChars_range_unsafe_tail b n str mul acc =
  if n ≤ b then acc
  else
    let m = n - 1 in
    fromChars_range_unsafe_tail b m str (mul * 10)
      (acc + fromChar_unsafe (strsub str m) * mul)
Termination
  WF_REL_TAC`measure (λ(b,n,_). n)`>>
  rw[]
End

Theorem fromChars_range_unsafe_tail_eq:
  ∀n l s mul acc.
  fromChars_range_unsafe_tail l (n+l) s mul acc =
  (fromChars_range_unsafe l n s) * mul + acc
Proof
  Induct
  >-
    rw[Once fromChars_range_unsafe_tail_def,fromChars_range_unsafe_def]>>
  rw[]>>
  simp[Once fromChars_range_unsafe_tail_def,ADD1,fromChars_range_unsafe_def]>>
  fs[ADD1]
QED

Theorem fromChars_range_unsafe_alt:
  fromChars_range_unsafe l n s =
  fromChars_range_unsafe_tail l (n+l) s 1 0
Proof
  rw[fromChars_range_unsafe_tail_eq]
QED

val result = translate fromChars_range_unsafe_tail_def;

val fromchars_range_unsafe_tail_side_def = theorem"fromchars_range_unsafe_tail_side_def";

Theorem fromchars_range_unsafe_tail_side_def[allow_rebind]:
  ∀a1 a0 a2 a3 a4.
  fromchars_range_unsafe_tail_side a0 a1 a2 a3 a4 ⇔
   ¬(a1 ≤ a0) ⇒
   (T ∧ a1 < 1 + strlen a2 ∧ 0 < strlen a2) ∧
   fromchars_range_unsafe_tail_side a0 (a1 − 1) a2 (a3 * 10)
     (a4 + fromChar_unsafe (strsub a2 (a1 − 1)) * a3)
Proof
  Induct>>
  rw[Once fromchars_range_unsafe_tail_side_def]>>
  simp[]>>eq_tac>>rw[ADD1]>>
  gvs[]
QED

val result = translate fromChars_range_unsafe_alt;

val res = translate_no_ind (mlintTheory.fromChars_unsafe_def
  |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);

Triviality fromChars_unsafe_ind:
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
  \\ fs [padLen_DEC_eq,ADD1]
QED

val _ = fromChars_unsafe_ind |> update_precondition;

val result = translate pb_parseTheory.fromString_unsafe_def;

val fromstring_unsafe_side_def = definition"fromstring_unsafe_side_def";
val fromchars_unsafe_side_def = theorem"fromchars_unsafe_side_def";
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

val r = translate int_start_def;

val _ = translate tokenize_fast_def;

val r = translate check_mark_qed_id_opt_def;
val r = translate check_mark_qed_id_def;

Definition check_mark_qed_id_pbc_def:
  check_mark_qed_id_pbc s = check_mark_qed_id (INL (strlit "pbc")) s
End

val r = translate check_mark_qed_id_pbc_def;

(* Just ensuring failing to parse line has the right index *)
Definition sub_one_def:
  sub_one (n:num) = if n = 0 then 0 else n - 1
End
val r = translate sub_one_def;

val parse_lsteps_aux = process_topdecs`
  fun parse_lsteps_aux f_ns fd lno acc =
    case TextIO.b_inputLineTokens #"\n" fd blanks tokenize_fast of
      None => raise Fail (format_failure lno "reached EOF while reading PBP steps")
    | Some s =>
    case parse_lstep_aux f_ns s of
      None => (List.rev acc,(f_ns,(s,lno+1)))
    | Some (Inl step,f_ns') =>
        parse_lsteps_aux f_ns' fd (lno+1) (step::acc)
    | Some (Inr c,f_ns') =>
        (case parse_lsteps_aux f_ns' fd (lno+1) [] of
          (pf,(f_ns'',(s,lno'))) =>
          case check_mark_qed_id_pbc s of
            None => raise Fail (format_failure (sub_one lno') "subproof not terminated with contradiction id")
          | Some id =>
            parse_lsteps_aux f_ns'' fd (lno') (Con c pf id::acc))`
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
    xmatch>>
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
      last_x_assum xapp_spec>>
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
    Cases_on`check_mark_qed_id_pbc s'`>>
    fs[OPTION_TYPE_def,check_mark_qed_id_pbc_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl >>
      simp[Once parse_lsteps_aux_thm,forwardFD_o,Fail_exn_def]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    rpt xlet_autop>>
    first_x_assum xapp_spec>>
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

val parse_lsteps = process_topdecs`
  fun parse_lsteps f_ns fd lno =
    parse_lsteps_aux f_ns fd lno []` |> append_prog;

Theorem parse_lsteps_spec:
  fns_TYPE a fns fnsv ∧
  NUM lno lnov ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_lsteps" (get_ml_prog_state()))
    [fnsv; fdv; lnov]
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
            parse_lsteps fns ss = SOME(acc',fns',s,rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_lsteps fns ss = NONE))
      )
Proof
  rw[]>>xcf "parse_lsteps" (get_ml_prog_state ())>>
  xlet_autop>>
  xapp>>xsimpl>>
  rpt (first_x_assum (irule_at Any))>>
  map_every qexists_tac [`lines`,`fs`,`fd`,`[]`,`emp`]>>
  simp[LIST_TYPE_def,PAIR_TYPE_def,parse_lsteps_def]>>
  xsimpl>>rw[]>>
  metis_tac[STDIO_INSTREAM_LINES_refl_gc,PAIR]
QED

val r = translate (parse_hash_num_def |> ONCE_REWRITE_RULE [GSYM sub_check_def]);

val parse_hash_num_side_def = fetch "-" "parse_hash_num_side_def";
val parse_hash_num_side = Q.prove(
  `∀x . parse_hash_num_side x <=> T`,
  Induct>>rw[Once parse_hash_num_side_def,sub_check_def]
  ) |> update_precondition;

val r = translate parse_subgoal_num_def;

val parse_subgoal_num_side_def = fetch "-" "parse_subgoal_num_side_def";
val parse_subgoal_num_side = Q.prove(
  `∀x . parse_subgoal_num_side x <=> T`,
  Induct>>rw[Once parse_subgoal_num_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate parse_proofgoal_def;

val r = translate mk_acc_def;

val r = translate mk_proofgoal_mark_def;

val parse_subproof_aux = process_topdecs`
  fun parse_subproof_aux f_ns fd lno acc =
    case parse_lsteps f_ns fd lno of
      (pf,(f_ns',(s,lno'))) =>
      let val acc' = mk_acc pf acc in
        case parse_proofgoal s of
          None => (List.rev acc', (f_ns', (s, lno')))
        | Some ind =>
          (case parse_lsteps f_ns' fd lno' of
            (pf,(f_ns'',(s,lno''))) =>
            case check_mark_qed_id (mk_proofgoal_mark ind) s of
              None => raise Fail (format_failure (sub_one lno'') "subproof not terminated with contradiction id")
            | Some id =>
              parse_subproof_aux f_ns'' fd lno'' ((Some (ind,id),pf)::acc')
              )
      end` |> append_prog

Theorem parse_subproof_aux_spec:
  ∀fns ss acc fd fdv lines lno lnov accv fs fnsv.
  fns_TYPE a fns fnsv ∧
  NUM lno lnov ∧
  pfs_TYPE acc accv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_subproof_aux" (get_ml_prog_state()))
    [fnsv; fdv; lnov; accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' acc' fns' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            (PAIR_TYPE pfs_TYPE
              (PAIR_TYPE (fns_TYPE a)
                (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NUM))) (acc',fns',s,lno') v ∧
            parse_subproof_aux fns ss acc = SOME(acc',fns',s,rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_subproof_aux fns ss acc = NONE))
      )
Proof
  ho_match_mp_tac parse_subproof_aux_ind>>
  rw[]>>
  simp[Once parse_subproof_aux_def]>>
  xcf "parse_subproof_aux" (get_ml_prog_state ())>>
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
            parse_lsteps fns (MAP toks_fast lines) = SOME(acc',fns',s,rest) ∧
            MAP toks_fast lines' = rest))
     (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_lsteps fns (MAP toks_fast lines) = NONE))
      )`
  >- (
    xapp>>xsimpl>>
    simp[LIST_TYPE_def]>>
    metis_tac[])
  >- (
    xsimpl>>
    rw[]>>
    simp[Once parse_subproof_aux_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl])>>
  simp[]>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xlet_auto
  >- (
    xsimpl>>
    simp (eq_lemmas()))>>
  rpt xlet_autop>>
  Cases_on`parse_proofgoal s`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[Once parse_subproof_aux_def,Fail_exn_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  xmatch>>
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
          parse_lsteps fns' rest = SOME(acc',fns'',s,rest') ∧
          MAP toks_fast lines'' = rest'))
    (λe.
       SEP_EXISTS k lines''.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines'' (forwardFD fs fd k) *
         &(Fail_exn e ∧ parse_lsteps fns' rest = NONE))
    )`
  >- (
    xapp>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`lines'`>>
    qexists_tac`forwardFD fs fd k`>>
    first_x_assum (irule_at Any)>>
    qexists_tac`fd`>>xsimpl>>
    simp[LIST_TYPE_def,PAIR_TYPE_def]>>
    rw[]
    >-(
      simp[forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
  >- (
    xsimpl>>rw[]>>
    simp[Once parse_subproof_aux_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl])>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  Cases_on`check_mark_qed_id (mk_proofgoal_mark x) s'`>>
  fs[OPTION_TYPE_def]>>xmatch
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    simp[Once parse_subproof_aux_def,Fail_exn_def]>>
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
  simp[Once parse_subproof_aux_def]>>
  simp[forwardFD_o]>>
  metis_tac[STDIO_INSTREAM_LINES_refl_gc]
QED

val parse_subproof_imp = process_topdecs`
  fun parse_subproof_imp f_ns fd lno =
    parse_subproof_aux f_ns fd lno []` |> append_prog

Theorem parse_subproof_imp_spec:
  fns_TYPE a fns fnsv ∧
  NUM lno lnov ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_subproof_imp" (get_ml_prog_state()))
    [fnsv; fdv; lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' acc' fns' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            (PAIR_TYPE pfs_TYPE
              (PAIR_TYPE (fns_TYPE a)
                (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NUM))) (acc',fns',s,lno') v ∧
            parse_subproof fns ss = SOME(acc',fns',s,rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_subproof fns ss = NONE))
      )
Proof
  rw[]>>xcf "parse_subproof_imp" (get_ml_prog_state ())>>
  xlet_autop>>
  xapp>>xsimpl>>
  rpt (first_x_assum (irule_at Any))>>
  map_every qexists_tac [`lines`,`fs`,`fd`,`[]`,`emp`]>>
  simp[LIST_TYPE_def,PAIR_TYPE_def,parse_subproof_def]>>
  xsimpl>>rw[]>>
  metis_tac[STDIO_INSTREAM_LINES_refl_gc,PAIR]
QED

val r = translate parse_scopetext_def;
val r = translate parse_scopehead_def;
val r = translate mk_scope_mark_def;

val parse_scope_aux = process_topdecs`
  fun parse_scope_aux f_ns fd lno acc =
    case parse_subproof_imp f_ns fd lno of
      (pf,(f_ns',(s,lno'))) =>
      let val acc' = mk_acc pf acc in
        case parse_scopehead s of
          None => (List.rev acc', (f_ns', (s, lno')))
        | Some ind =>
          (case parse_subproof_imp f_ns' fd lno' of
            (pf,(f_ns'',(s,lno''))) =>
            if check_end (mk_scope_mark ind) s
            then
              parse_scope_aux f_ns'' fd lno'' ((Some ind,pf)::acc')
            else
              raise Fail (format_failure (sub_one lno'') "scope not terminated with end (no id allowed)"))
      end` |> append_prog

val mk_scope_mark_v_thm = fetch "-" "mk_scope_mark_v_thm"
  |> Q.GEN `a` |> Q.ISPEC`INT`;

Theorem parse_scope_aux_spec:
  ∀fns ss acc fd fdv lines lno lnov accv fs fnsv.
  fns_TYPE a fns fnsv ∧
  NUM lno lnov ∧
  scpfs_TYPE acc accv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_scope_aux" (get_ml_prog_state()))
    [fnsv; fdv; lnov; accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' acc' fns' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            (PAIR_TYPE scpfs_TYPE
              (PAIR_TYPE (fns_TYPE a)
                (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NUM))) (acc',fns',s,lno') v ∧
            parse_scope_aux fns ss acc = SOME(acc',fns',s,rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_scope_aux fns ss acc = NONE))
      )
Proof
  ho_match_mp_tac parse_scope_aux_ind>>
  rw[]>>
  simp[Once parse_scope_aux_def]>>
  xcf "parse_scope_aux" (get_ml_prog_state ())>>
  xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' acc' fns' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            PAIR_TYPE pfs_TYPE
              (PAIR_TYPE (fns_TYPE a)
              (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
                NUM)) (acc',fns',s,lno') v ∧
            parse_subproof fns (MAP toks_fast lines) = SOME(acc',fns',s,rest) ∧
            MAP toks_fast lines' = rest))
     (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_subproof fns (MAP toks_fast lines) = NONE))
      )`
  >- (
    xapp>>xsimpl>>
    simp[LIST_TYPE_def]>>
    metis_tac[])
  >- (
    xsimpl>>
    rw[]>>
    simp[Once parse_scope_aux_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl])>>
  simp[]>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xlet_auto
  >- (
    xsimpl>>
    irule EqualityType_PAIR_TYPE>>
    simp (eq_lemmas())>>
    irule EqualityType_LIST_TYPE>>
    simp (eq_lemmas()))>>
  rpt xlet_autop>>
  Cases_on`parse_scopehead s`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[Once parse_scope_aux_def,Fail_exn_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  xmatch>>
  xlet`(POSTve
    (λv.
       SEP_EXISTS k lines'' acc' fns'' s lno' rest'.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines'' (forwardFD fs fd k) *
       &(
          PAIR_TYPE pfs_TYPE
            (PAIR_TYPE (fns_TYPE a)
            (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
              NUM))
            (acc',fns'',s,lno') v ∧
          parse_subproof fns' rest = SOME(acc',fns'',s,rest') ∧
          MAP toks_fast lines'' = rest'))
    (λe.
       SEP_EXISTS k lines''.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines'' (forwardFD fs fd k) *
         &(Fail_exn e ∧ parse_subproof fns' rest = NONE))
    )`
  >- (
    xapp>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`lines'`>>
    qexists_tac`forwardFD fs fd k`>>
    first_x_assum (irule_at Any)>>
    qexists_tac`fd`>>xsimpl>>
    simp[LIST_TYPE_def,PAIR_TYPE_def]>>
    rw[]
    >-(
      simp[forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
  >- (
    xsimpl>>rw[]>>
    simp[Once parse_scope_aux_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl])>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xlet`POSTv v.
    STDIO (forwardFD fs fd k) *
    INSTREAM_LINES #"\n" fd fdv lines'' (forwardFD fs fd k) *
    &(LIST_TYPE (SUM_TYPE STRING_TYPE INT) (mk_scope_mark x) v)`
  >- (
    xapp_spec mk_scope_mark_v_thm>>xsimpl>>
    metis_tac[])>>
  rpt xlet_autop>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    simp[Once parse_scope_aux_def,Fail_exn_def]>>
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
  simp[Once parse_scope_aux_def]>>
  simp[forwardFD_o]>>
  metis_tac[STDIO_INSTREAM_LINES_refl_gc]
QED

val parse_scope_imp = process_topdecs`
  fun parse_scope_imp f_ns fd lno =
    parse_scope_aux f_ns fd lno []` |> append_prog

Theorem parse_scope_imp_spec:
  fns_TYPE a fns fnsv ∧
  NUM lno lnov ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_scope_imp" (get_ml_prog_state()))
    [fnsv; fdv; lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' acc' fns' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            (PAIR_TYPE scpfs_TYPE
              (PAIR_TYPE (fns_TYPE a)
                (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NUM))) (acc',fns',s,lno') v ∧
            parse_scope fns ss = SOME(acc',fns',s,rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_scope fns ss = NONE))
      )
Proof
  rw[]>>xcf "parse_scope_imp" (get_ml_prog_state ())>>
  xlet_autop>>
  xapp>>xsimpl>>
  rpt (first_x_assum (irule_at Any))>>
  map_every qexists_tac [`lines`,`fs`,`fd`,`[]`,`emp`]>>
  simp[LIST_TYPE_def,PAIR_TYPE_def,parse_scope_def]>>
  xsimpl>>rw[]>>
  metis_tac[STDIO_INSTREAM_LINES_refl_gc,PAIR]
QED

val r = translate parse_red_header_red_def;

Definition check_mark_qed_id_opt_red_def:
  check_mark_qed_id_opt_red s = check_mark_qed_id_opt (INL (strlit "red")) s
End

val r = translate check_mark_qed_id_opt_red_def;

val parse_sstep_imp = process_topdecs`
  fun parse_sstep_imp fns fd lno =
    case TextIO.b_inputLineTokens #"\n" fd blanks tokenize_fast of
      None =>
      raise Fail (format_failure lno "Unexpected EOF when parsing proof steps")
    | Some s =>
    (case parse_lstep_aux fns s of
      None =>
        (case parse_red_header_red fns s of
          None => (Inl s, (fns, lno+1))
        | Some (c,(s,fns')) =>
          case parse_scope_imp fns' fd (lno+1) of
            (pf,(fns'',(h,lno'))) =>
            (case check_mark_qed_id_opt_red h of
              None =>
                raise Fail (format_failure (sub_one lno') "Incorrectly terminated redundancy step")
            | Some idopt =>
              (Inr (Red c s pf idopt),(fns'',lno'))))
    | Some (Inl step,fns') => (Inr (Lstep step),(fns',lno+1))
    | Some (Inr c,fns') =>
        case parse_lsteps fns' fd (lno+1) of
        (pf,(fns'',(res,lno'))) =>
        (case check_mark_qed_id_pbc res of
            None => raise Fail (format_failure (sub_one lno') "subproof not terminated with contradiction id")
          | Some n =>
            (Inr (Lstep (Con c pf n)), (fns'', lno')))
        )` |> append_prog

Theorem parse_sstep_imp_spec:
  !ss fd fdv lines lno lnov fs fns fnsv.
  fns_TYPE a fns fnsv ∧
  NUM lno lnov ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_sstep_imp" (get_ml_prog_state()))
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
  xcf "parse_sstep_imp" (get_ml_prog_state ())>>
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
  fs[OPTION_TYPE_SPLIT]
  >- (
    xmatch>>
    rpt xlet_autop>>
    gvs[OPTION_TYPE_SPLIT]
    >- (
      xmatch>>
      rpt xlet_autop>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def,SUM_TYPE_def]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    `∃cc ss fns'. y = (cc,ss,fns')` by metis_tac[PAIR]>>
    gvs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' acc' fns'' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            (PAIR_TYPE scpfs_TYPE
              (PAIR_TYPE (fns_TYPE a)
                (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NUM))) (acc',fns'',s,lno') v ∧
            parse_scope fns' (MAP toks_fast ls) = SOME(acc',fns'',s,rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_scope fns' (MAP toks_fast ls)= NONE))
      )`
    >- (
      xapp>>xsimpl>>
      rpt (first_x_assum (irule_at Any))>>
      qexists_tac`ls`>>
      qexists_tac`forwardFD fs fd k`>>
      qexists_tac`fd`>>
      qexists_tac`emp`>>
      xsimpl>>
      rw[]
      >- (
        first_x_assum (irule_at Any)>>
        gvs[PAIR_TYPE_def,forwardFD_o]>>
        metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
      simp[forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])
    >- (
      xsimpl>>
      metis_tac[STDIO_INSTREAM_LINES_refl])>>
    gvs[PAIR_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    pop_assum mp_tac>>
    simp[Once OPTION_TYPE_SPLIT,check_mark_qed_id_opt_red_def]>>
    strip_tac>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl>>
      metis_tac[Fail_exn_def,STDIO_INSTREAM_LINES_refl_gc])>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[NPBC_CHECK_SSTEP_TYPE_def,NPBC_CHECK_LSTEP_TYPE_def,SUM_TYPE_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  pop_assum mp_tac>>
  simp[Once PAIR_TYPE_SPLIT]>>
  strip_tac>>
  gvs[]>>
  Cases_on`x1`>>gvs[SUM_TYPE_def]>>xmatch
  >- ( (* INL *)
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def,NPBC_CHECK_SSTEP_TYPE_def,SUM_TYPE_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  (* INR *)
  rpt xlet_autop>>
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
            parse_lsteps x2 (MAP toks_fast ls) = SOME(acc',fns',s,rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_lsteps x2 (MAP toks_fast ls) = NONE))
      )`
  >- (
    xapp>>
    xsimpl>>
    rpt (first_x_assum (irule_at Any))>>
    qexists_tac`ls`>>
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`fd`>>
    qexists_tac`emp`>>
    xsimpl>>
    rw[]
    >- (
      first_x_assum (irule_at Any)>>
      gvs[PAIR_TYPE_def,forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
  >- (
    xsimpl>>
    gvs[]>>rw[]>>
    metis_tac[STDIO_INSTREAM_LINES_refl])>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  gvs[OPTION_TYPE_SPLIT]>>xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    gvs[check_mark_qed_id_pbc_def]>>
    metis_tac[Fail_exn_def,STDIO_INSTREAM_LINES_refl_gc])>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  gvs[check_mark_qed_id_pbc_def]>>
  simp[NPBC_CHECK_SSTEP_TYPE_def,NPBC_CHECK_LSTEP_TYPE_def,SUM_TYPE_def]>>
  metis_tac[STDIO_INSTREAM_LINES_refl_gc]
QED

(* Handling def_order *)

val res = translate check_open_def;
val res = translate check_end_full_def;
val res = translate pre_order_symbols_def;

val read_open = process_topdecs`
  fun read_open lno h fd acc =
    let val l = TextIO.b_inputLineTokens #"\n" fd blanks tokenize_fast in
    case l of None =>
      raise Fail (format_failure lno ("reached EOF while looking for def_order opening line:" ^ h))
    | Some x =>
      if check_open h x then (x::acc,lno+1)
      else read_open (lno+1) h fd (x::acc)
    end` |> append_prog;

Theorem read_open_spec:
  !h ss acc lines lno lnov hv accv fs.
  NUM lno lnov ∧
  STRING_TYPE h hv ∧
  LIST_TYPE
    (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) acc accv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "read_open" (get_ml_prog_state()))
    [lnov; hv; fdv; accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            case read_open h ss acc of
              NONE => F
            | SOME (acc',rest) =>
                PAIR_TYPE
                  (LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
                  NUM (acc',lno') v ∧
                MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ read_open h ss acc = NONE))
      )
Proof
  Induct_on`ss`>>
  rw[]>>xcf "read_open" (get_ml_prog_state ())
  >- (
    simp[read_open_def]>>
    xlet ‘(POSTv v.
        SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
            &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    >- (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac ‘emp’
      \\ qexists_tac ‘[]’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl)>>
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
  simp[read_open_def]>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def,LIST_TYPE_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  rpt xlet_autop>>
  xapp>>xsimpl>>
  rpt (first_x_assum (irule_at Any))>>
  qexists_tac`forwardFD fs fd k`>>
  qexists_tac`h::acc`>>
  qexists_tac`emp`>>
  simp[LIST_TYPE_def]>>xsimpl>>
  rw[]>>gvs[AllCasePreds(),PAIR_TYPE_def,forwardFD_o]>>
  metis_tac[STDIO_INSTREAM_LINES_refl_gc]
QED

val read_end = process_topdecs`
  fun read_end lno h fd acc =
    let val l = TextIO.b_inputLineTokens #"\n" fd blanks tokenize_fast in
    case l of None =>
      raise Fail (format_failure lno ("reached EOF while looking for def_order ending line:" ^ h))
    | Some x =>
      if check_end_full h x then (x::acc,lno+1)
      else read_end (lno+1) h fd (x::acc)
    end` |> append_prog;

Theorem read_end_spec:
  !h ss acc lines lno lnov hv accv fs.
  NUM lno lnov ∧
  STRING_TYPE h hv ∧
  LIST_TYPE
    (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) acc accv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "read_end" (get_ml_prog_state()))
    [lnov; hv; fdv; accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            case read_end h ss acc of
              NONE => F
            | SOME (acc',rest) =>
                PAIR_TYPE
                  (LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
                  NUM (acc',lno') v ∧
                MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ read_end h ss acc = NONE))
      )
Proof
  Induct_on`ss`>>
  rw[]>>xcf "read_end" (get_ml_prog_state ())
  >- (
    simp[read_end_def]>>
    xlet ‘(POSTv v.
        SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
            &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    >- (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac ‘emp’
      \\ qexists_tac ‘[]’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl)>>
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
  simp[read_end_def]>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def,LIST_TYPE_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  rpt xlet_autop>>
  xapp>>xsimpl>>
  rpt (first_x_assum (irule_at Any))>>
  qexists_tac`forwardFD fs fd k`>>
  qexists_tac`h::acc`>>
  qexists_tac`emp`>>
  simp[LIST_TYPE_def]>>xsimpl>>
  rw[]>>gvs[AllCasePreds(),PAIR_TYPE_def,forwardFD_o]>>
  metis_tac[STDIO_INSTREAM_LINES_refl_gc]
QED

val read_while = process_topdecs`
  fun read_while lno hs fd acc =
    case hs of
      [] => (List.rev acc,lno)
    | h::hs =>
      case h of
        Inl h =>
          (case read_open lno h fd acc of (acc',lno') =>
            read_while lno' hs fd acc')
      | Inr h =>
          (case read_end lno h fd acc of (acc',lno') =>
            read_while lno' hs fd acc')` |> append_prog;

Theorem read_while_spec:
  !hs ss acc lines lno lnov hsv accv fs.
  NUM lno lnov ∧
  LIST_TYPE (SUM_TYPE STRING_TYPE STRING_TYPE) hs hsv ∧
  LIST_TYPE
    (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) acc accv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "read_while" (get_ml_prog_state()))
    [lnov; hsv; fdv; accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            case read_while hs ss acc of
              NONE => F
            | SOME (acc',rest) =>
                PAIR_TYPE
                  (LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
                  NUM (acc',lno') v ∧
                MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ read_while hs ss acc = NONE))
      )
Proof
  Induct_on`hs`>>
  rw[]>>xcf "read_while" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>xmatch
  >- (
    xlet_autop>>xcon>>
    simp[read_while_def,PAIR_TYPE_def]>>xsimpl>>
    qexists_tac`0`>>simp[]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  simp[read_while_def]>>
  Cases_on`h`>>fs[SUM_TYPE_def]>>xmatch
  >- (
    xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            case read_open x (MAP toks_fast lines) acc of
              NONE => F
            | SOME (acc',rest) =>
                PAIR_TYPE
                  (LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
                  NUM (acc',lno') v ∧
                MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ read_open x (MAP toks_fast lines) acc = NONE))
      )`
    >- (
      xapp>>simp[]>>
      metis_tac[])
    >- (xsimpl>>
      metis_tac[STDIO_INSTREAM_LINES_refl])>>
    gvs[AllCasePreds(),PAIR_TYPE_def]>>
    xmatch>>
    xapp>>xsimpl>>
    rpt (first_x_assum (irule_at Any))>>
    qexists_tac`lines'`>>
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`emp`>>
    xsimpl>>rw[]>>simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
  >- (
    xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            case read_end y (MAP toks_fast lines) acc of
              NONE => F
            | SOME (acc',rest) =>
                PAIR_TYPE
                  (LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
                  NUM (acc',lno') v ∧
                MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ read_end y (MAP toks_fast lines) acc = NONE))
      )`
    >- (
      xapp>>simp[]>>
      metis_tac[])
    >- (xsimpl>>
      metis_tac[STDIO_INSTREAM_LINES_refl])>>
    gvs[AllCasePreds(),PAIR_TYPE_def]>>
    xmatch>>
    xapp>>xsimpl>>
    rpt (first_x_assum (irule_at Any))>>
    qexists_tac`lines'`>>
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`emp`>>
    xsimpl>>rw[]>>simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
QED

val res = translate pb_parseTheory.parse_vars_line_aux_def;
val res = translate pb_parseTheory.parse_vars_line_def;
val res = translate parse_vars_aux_def;
val res = translate parse_vars_block_def;

val res = translate parse_lsteps_aux_def;
val res = translate parse_lsteps_def;
val res = translate parse_subproof_aux_def;
val res = translate parse_subproof_def;
val res = translate parse_scope_aux_def;
val res = translate parse_scope_def;
val res = translate parse_sstep_def;

val res = translate parse_spec_aux_def;
val res = translate parse_spec_block_def;
val res = translate parse_def_aux_def;
val res = translate parse_def_block_def;

val res = translate parse_spec_def_block_def;

val res = translate parse_trans_aux_def;
val res = translate parse_trans_block_aux_def;
val res = translate check_qed_def;
val res = translate parse_proof_block_def;
val res = translate parse_trans_block_def;
val res = translate parse_refl_block_def;
val res = translate parse_trans_refl_block_def;

val res = translate parse_pre_order_pure_def;

val parse_pre_order = process_topdecs`
  fun parse_pre_order fns fd lno =
  case read_while lno pre_order_symbols fd [] of
    (preord,lno') =>
  case parse_pre_order_pure fns preord of
    None =>
      raise Fail (format_failure lno ("failed to parse order definition starting at line."))
  | Some (vars,(gspec,(f,(pfr,(pft,fns))))) =>
    (vars,(gspec,(f,(pfr,(pft,(fns,lno'))))))` |> append_prog;

Theorem parse_pre_order_spec:
  NUM lno lnov ∧
  fns_TYPE a fns fnsv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_pre_order" (get_ml_prog_state()))
    [fnsv;fdv;lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' res
           vars gspec f pfr pft fns' rest lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            parse_pre_order fns ss =
              SOME (vars,gspec,f,pfr,pft,fns',rest) ∧
            PAIR_TYPE
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE NUM)))
            (PAIR_TYPE
              (LIST_TYPE
                   (PAIR_TYPE constraint_TYPE
                      (PAIR_TYPE subst_raw_TYPE
                         (PAIR_TYPE scpfs_TYPE (OPTION_TYPE NUM)))))
            (PAIR_TYPE (LIST_TYPE constraint_TYPE)
            (PAIR_TYPE pfs_TYPE
            (PAIR_TYPE
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE (LIST_TYPE NUM)
                  (PAIR_TYPE (LIST_TYPE NUM) pfs_TYPE)))
            (PAIR_TYPE
              (fns_TYPE a)
              NUM)))))
            (vars,gspec,f,pfr,pft,fns',lno') v ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(Fail_exn e ∧ parse_pre_order fns ss = NONE)))
Proof
  rw[]>>
  xcf "parse_pre_order" (get_ml_prog_state ())>>
  xlet_autop>>
  xlet `(POSTve
      (λv.
         SEP_EXISTS k lines' lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            case read_while pre_order_symbols (MAP toks_fast lines) [] of
              NONE => F
            | SOME (acc',rest) =>
                PAIR_TYPE
                  (LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
                  NUM (acc',lno') v ∧
                MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ read_while pre_order_symbols (MAP toks_fast lines) [] = NONE))
      )`
  >- (
    xapp>>xsimpl>>
    assume_tac (fetch "-" "pre_order_symbols_v_thm")>>
    rpt(first_x_assum (irule_at Any))>>
    simp[LIST_TYPE_def])
  >- (
    xsimpl>>
    simp[parse_pre_order_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl])>>
  gvs[AllCasePreds(),PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  simp[parse_pre_order_def]>>
  TOP_CASE_TAC>>gvs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    metis_tac[Fail_exn_def,STDIO_INSTREAM_LINES_refl_gc])>>
  PairCases_on`x`>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  simp[PAIR_TYPE_def]>>
  metis_tac[Fail_exn_def,STDIO_INSTREAM_LINES_refl_gc]
QED

val res = translate parse_delc_header_def;
val parse_delc_header_side = Q.prove(
  `∀x y. parse_delc_header_side x y <=> T`,
  simp[fetch "-" "parse_delc_header_side_def"]>>
  rw[]>>
  intLib.ARITH_TAC) |> update_precondition;

val res = translate OPTION_BIND_def;

val res = translate (strip_obju_end_def |> SIMP_RULE std_ss [GSYM mllistTheory.take_def,GSYM mllistTheory.drop_def]);
val res = translate normalise_obj_def;
val res = translate parse_obj_term_def;
val res = translate parse_obj_term_npbc_def;

val res = translate parse_b_obj_term_npbc_def;

val res = translate parse_preserve_def;

val res = translate parse_to_core_def;

val res = translate parse_strengthen_def;

val res = translate split_lit_def;
val res = translate parse_lits_line_aux_def;
val res = translate parse_load_order_def;

val res = translate parse_assg_def;
val res = translate parse_sol_def;

val res = translate parse_eobj_def;

val res = translate parse_cstep_head_def;

val PB_PARSE_PAR_TYPE_def = theorem"PB_PARSE_PAR_TYPE_def";

Definition check_mark_qed_id_opt_dom_def:
  check_mark_qed_id_opt_dom s = check_mark_qed_id_opt (INL (strlit "dom")) s
End

val r = translate check_mark_qed_id_opt_dom_def;

Definition check_mark_qed_id_opt_delc_def:
  check_mark_qed_id_opt_delc s = check_mark_qed_id_opt (INL (strlit "delc")) s
End

val r = translate check_mark_qed_id_opt_delc_def;

Definition check_mark_qed_id_opt_obju_def:
  check_mark_qed_id_opt_obju s = check_mark_qed_id_opt (INL (strlit "obju")) s
End

val r = translate check_mark_qed_id_opt_obju_def;

val parse_cstep = process_topdecs`
  fun parse_cstep fns fd lno =
    case parse_sstep_imp fns fd lno of
      (Inr sstep, (fns',lno')) =>
        (Inr (Sstep sstep), (fns',lno'))
    | (Inl s, (fns',lno')) =>
    (case parse_cstep_head fns' s of
      None => (Inl s, (fns',lno'))
    | Some (Done cstep,fns'') => (Inr cstep, (fns'', lno'))
    | Some (Dompar c s,fns'') =>
        (case parse_scope_imp fns'' fd (lno') of
            (pf,(fns''',(h,lno''))) =>
            (case check_mark_qed_id_opt_dom h of
              None =>
                raise Fail (format_failure (sub_one lno'') "Incorrectly terminated dominance step")
            | Some idopt =>
              (Inr (Dom c s pf idopt),(fns''',lno''))))
    | Some (Checkeddeletepar n s, fns'') =>
        (case parse_scope_imp fns'' fd (lno') of
            (pf,(fns''',(h,lno''))) =>
            (case check_mark_qed_id_opt_delc h of
              None =>
                raise Fail (format_failure (sub_one lno'') "Incorrectly terminated checked deletion step")
            | Some idopt =>
              (Inr (Checkeddelete n s pf idopt),(fns''',lno''))))
    | Some (Storeorderpar name, fns'') =>
        (case parse_pre_order fns'' fd lno' of
          (vars,(gspec,(f,(pfr,(pft,(fns''',lno'')))))) =>
          (Inr (Storeorder name vars gspec f pfr pft), (fns''', lno'')))
    | Some (Changeobjpar b f, fns'') =>
        (case parse_subproof_imp fns'' fd lno' of
          (pf,(fns''',(s,lno''))) =>
            (case check_mark_qed_id_opt_obju s of
              Some None =>
              (Inr (Changeobj b f pf),(fns''',lno''))
            | _ =>
                raise Fail (format_failure (sub_one lno'') "Incorrectly terminated objective update step")))
    | Some (Changeprespar b x c, fns'') =>
        raise Fail (format_failure lno "Parsing change proj set not yet supported")
    )
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
    qmatch_goalsub_abbrev_tac`INSTREAM_LINES #"\n" _ _ lines1 fs1`>>
    xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' acc' fns' s lno' rest.
         STDIO (forwardFD fs1 fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs1 fd k) *
         &(
            (PAIR_TYPE scpfs_TYPE
              (PAIR_TYPE (fns_TYPE a)
                (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NUM))) (acc',fns',s,lno') v ∧
            parse_scope r (MAP toks_fast lines1) = SOME(acc',fns',s,rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs1 fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs1 fd k) *
           &(Fail_exn e ∧ parse_scope r (MAP toks_fast lines1) = NONE))
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
    TOP_CASE_TAC>>gvs[check_mark_qed_id_opt_dom_def,OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl>>
      unabbrev_all_tac>>
      simp[Fail_exn_def,forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def,NPBC_CHECK_CSTEP_TYPE_def]>>
    unabbrev_all_tac>>simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
  >- (
    rpt xlet_autop>>
    qmatch_goalsub_abbrev_tac`INSTREAM_LINES #"\n" _ _ lines1 fs1`>>
    xlet`
      (POSTve
      (λv.
         SEP_EXISTS k lines' res
           vars gspec f pfr pft fns' rest lno'.
         STDIO (forwardFD fs1 fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs1 fd k) *
         &(
            parse_pre_order r (MAP toks_fast lines1) =
              SOME (vars,gspec,f,pfr,pft,fns',rest) ∧
            PAIR_TYPE
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE NUM)))
            (PAIR_TYPE
              (LIST_TYPE
                   (PAIR_TYPE constraint_TYPE
                      (PAIR_TYPE subst_raw_TYPE
                         (PAIR_TYPE scpfs_TYPE (OPTION_TYPE NUM)))))
            (PAIR_TYPE (LIST_TYPE constraint_TYPE)
            (PAIR_TYPE pfs_TYPE
            (PAIR_TYPE
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE (LIST_TYPE NUM)
                  (PAIR_TYPE (LIST_TYPE NUM) pfs_TYPE)))
            (PAIR_TYPE
              (fns_TYPE a)
              NUM)))))
            (vars,gspec,f,pfr,pft,fns',lno') v ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs1 fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs1 fd k) *
         &(Fail_exn e ∧ parse_pre_order r (MAP toks_fast lines1) = NONE)))`
    >- (
      xapp>>
      metis_tac[])
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
    qmatch_goalsub_abbrev_tac`INSTREAM_LINES #"\n" _ _ lines1 fs1`>>
    xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' acc' fns' s lno' rest.
         STDIO (forwardFD fs1 fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs1 fd k) *
         &(
            (PAIR_TYPE scpfs_TYPE
              (PAIR_TYPE (fns_TYPE a)
                (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NUM))) (acc',fns',s,lno') v ∧
            parse_scope r (MAP toks_fast lines1) = SOME(acc',fns',s,rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs1 fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs1 fd k) *
           &(Fail_exn e ∧ parse_scope r (MAP toks_fast lines1) = NONE))
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
    TOP_CASE_TAC>>gvs[check_mark_qed_id_opt_delc_def,OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl>>
      unabbrev_all_tac>>
      simp[Fail_exn_def,forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def,NPBC_CHECK_CSTEP_TYPE_def]>>
    unabbrev_all_tac>>simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
  >- (
    qmatch_goalsub_abbrev_tac`INSTREAM_LINES #"\n" _ _ lines1 fs1`>>
    xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' acc' fns' s lno' rest.
         STDIO (forwardFD fs1 fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs1 fd k) *
         &(
            (PAIR_TYPE pfs_TYPE
              (PAIR_TYPE (fns_TYPE a)
                (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NUM))) (acc',fns',s,lno') v ∧
            parse_subproof r (MAP toks_fast lines1) = SOME(acc',fns',s,rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs1 fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs1 fd k) *
           &(Fail_exn e ∧ parse_subproof r (MAP toks_fast lines1) = NONE))
      )`
    >- (
      xapp>>
      xsimpl>>
      metis_tac[LIST_TYPE_def])
    >- (
      xsimpl>>
      unabbrev_all_tac>>simp[forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl]) >>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    TOP_CASE_TAC>>gvs[check_mark_qed_id_opt_obju_def,OPTION_TYPE_def]
    >- (
      xmatch>>
      rpt xlet_autop>>
      xraise>>xsimpl>>
      unabbrev_all_tac>>
      simp[Fail_exn_def,forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    reverse TOP_CASE_TAC>>
    gvs[check_mark_qed_id_opt_obju_def,OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl>>
      unabbrev_all_tac>>
      simp[Fail_exn_def,forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def,NPBC_CHECK_CSTEP_TYPE_def]>>
    unabbrev_all_tac>>simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
  >>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    gvs[Fail_exn_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc]
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

Theorem read_open_LENGTH:
  ∀h ss acc.
  read_open h ss acc = SOME (acc',ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  Induct_on`ss`>>
  rw[read_open_def]>>
  first_x_assum drule>>simp[]
QED

Theorem read_end_LENGTH:
  ∀h ss acc.
  read_end h ss acc = SOME (acc',ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  Induct_on`ss`>>
  rw[read_end_def]>>
  first_x_assum drule>>simp[]
QED

Theorem read_while_LENGTH:
  ∀hs ss acc.
  read_while hs ss acc = SOME (ss',rest) ⇒
  LENGTH rest + LENGTH hs ≤ LENGTH ss
Proof
  Induct>>rw[read_while_def]>>
  gvs[AllCaseEqs()]>>
  first_x_assum drule_all>>
  imp_res_tac read_open_LENGTH>>
  imp_res_tac read_end_LENGTH>>
  fs[]
QED

Theorem parse_pre_order_LENGTH:
  parse_pre_order fns ss = SOME (a,b,c,d,e,fns',ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  rw[parse_pre_order_def]>>
  gvs[AllCaseEqs()]>>
  drule read_while_LENGTH>>
  EVAL_TAC>>simp[]
QED

(* Repeatedly parse a line and run the cstep checker,
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
  imp_res_tac parse_sstep_LENGTH>>
  fs[parse_scope_def]>>
  imp_res_tac parse_scope_aux_LENGTH>>
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
    fnsv lno lnov fmllsv zerosv indsv pcv lines fs fmlv vimaplsv vimapv vomapv.
  fns_TYPE a fns fnsv ∧
  NUM lno lnov ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NPBC_CHECK_PROOF_CONF_TYPE pc pcv ∧
  LIST_REL (OPTION_TYPE vimapn_TYPE) vimap vimaplsv ∧
  vomap_TYPE vomap vomapv ∧
  EVERY (λw. w = 0w) zeros ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat''" (get_ml_prog_state()))
    [fnsv; fdv; lnov; fmlv; zerosv; indsv; vimapv; vomapv; pcv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs *
      ARRAY fmlv fmllsv * W8ARRAY zerosv zeros *
      ARRAY vimapv vimaplsv)
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
      qexists_tac`ARRAY fmlv fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv`>>
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
         ARRAY fmlv fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv *
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
    qexists_tac`ARRAY fmlv fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv`>>
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
         SEP_EXISTS fmlv' fmllsv' zerosv' zeros'
           vimapv' vimaplsv'.
           W8ARRAY zerosv' zeros' * ARRAY fmlv' fmllsv' *
           ARRAY vimapv' vimaplsv' * STDIO (forwardFD fs fd k) *
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
                     (PAIR_TYPE
                       (λl v.
                         LIST_REL (OPTION_TYPE vimapn_TYPE) l vimaplsv' ∧
                         v = vimapv')
                        (PAIR_TYPE vomap_TYPE NPBC_CHECK_PROOF_CONF_TYPE))))
               res v')
    (λe.
         SEP_EXISTS fmlv' fmllsv'.
           ARRAY fmlv' fmllsv' *
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧
            check_cstep_list y fmlls zeros inds vimap vomap pc = NONE))`
  >- (
    xapp>>
    xsimpl>>reverse (rw[])>>
    rpt(first_x_assum (irule_at Any))>>
    xsimpl>>
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
      xs (update_vimap acc k (FST x)))
End

Theorem fold_update_vimap_enum_FOLDL:
  ∀xs k acc.
  fold_update_vimap_enum k xs acc =
  (FOLDL (λacc (i,v). update_vimap acc i (FST v)) acc (enumerate k xs))
Proof
  Induct>>rw[fold_update_vimap_enum_def,miscTheory.enumerate_def]
QED

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
  if strip_term_line y = SOME ^endtrm
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
    strlit "unable to parse line at (parse error may be later for output/conclusion section): " ^
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
    fml' inds' pres' obj' bound' dbound' chk'
    fmlt prest objt
    output hconcl =
  format_err
  (check_output_arr fml' inds'
    pres' obj' bound' dbound' chk' fmlt prest objt output)
  (check_hconcl_arr fml obj fml' obj' bound' dbound' hconcl)`
  |> append_prog;

Theorem check_output_hconcl_arr_spec:
  LIST_TYPE constraint_TYPE fml fmlv ∧
  obj_TYPE obj objv ∧
  (LIST_TYPE NUM) inds1 inds1v ∧
  obj_TYPE obj1 obj1v ∧
  pres_TYPE pres1 pres1v ∧
  OPTION_TYPE INT bound1 bound1v ∧
  OPTION_TYPE INT dbound1 dbound1v ∧
  BOOL chk1 chk1v ∧
  LIST_TYPE constraint_TYPE fmlt fmltv ∧
  pres_TYPE prest prestv ∧
  obj_TYPE objt objtv ∧
  PBC_OUTPUT_TYPE output outputv ∧
  NPBC_CHECK_HCONCL_TYPE hconcl hconclv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_output_hconcl_arr" (get_ml_prog_state()))
    [fmlv; objv;
      fml1v; inds1v; pres1v; obj1v; bound1v; dbound1v; chk1v;
      fmltv; prestv; objtv;
      outputv; hconclv]
    (ARRAY fml1v fmllsv)
    (POSTv v.
        ARRAY fml1v fmllsv *
        &(
        ∃s.
        (OPTION_TYPE STRING_TYPE)
        (if check_output_list fmlls inds1 pres1 obj1
          bound1 dbound1 chk1 fmlt prest objt output ∧
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

(* Parse the conclusion from the rest of the file and check it *)
val run_concl_file = process_topdecs`
  fun run_concl_file fd f_ns lno s
    fml obj
    fml' inds' pres' obj' bound' dbound' chk'
    fmlt prest objt =
  let
    val ls = TextIO.b_inputAllTokens #"\n" fd blanks tokenize
  in
    case parse_output_concl s f_ns ls of
      None => Inl (format_failure (sub_one lno) (mk_parse_err s))
    | Some (output,hconcl) =>
      case
        check_output_hconcl_arr
        fml obj
        fml' inds' pres' obj' bound' dbound' chk'
        fmlt prest objt
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
  pres_TYPE pres1 pres1v ∧
  OPTION_TYPE INT bound1 bound1v ∧
  OPTION_TYPE INT dbound1 dbound1v ∧
  BOOL chk1 chk1v ∧
  LIST_TYPE constraint_TYPE fmlt fmltv ∧
  obj_TYPE objt objtv ∧
  pres_TYPE prest prestv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "run_concl_file" (get_ml_prog_state()))
    [fdv; fnsv;lnov;sv;
      fmlv; objv; fml1v; inds1v; pres1v; obj1v; bound1v; dbound1v; chk1v;
      fmltv; prestv; objtv]
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
            pres1 obj1 bound1 dbound1 chk1 fmlt prest objt output ∧
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

val fold_update_vimap_enum_arr = process_topdecs `
  fun fold_update_vimap_enum_arr k ls acc =
  case ls of [] => acc
  | (x::xs) =>
    fold_update_vimap_enum_arr (k+1)
      xs (update_vimap_arr acc k (fst x))` |> append_prog;

Theorem fold_update_vimap_enum_arr_spec:
  ∀ls lsv vimap vimapv vimaplsv k kv.
  NUM k kv ∧
  LIST_TYPE constraint_TYPE ls lsv ∧
  LIST_REL (OPTION_TYPE vimapn_TYPE) vimap vimaplsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "fold_update_vimap_enum_arr" (get_ml_prog_state()))
    [kv; lsv; vimapv]
    (ARRAY vimapv vimaplsv)
    (POSTv v.
       SEP_EXISTS vimaplsv'.
        ARRAY v vimaplsv' *
        &(LIST_REL (OPTION_TYPE vimapn_TYPE)
          (mk_vimap vimap (enumerate k ls)) vimaplsv'))
Proof
  simp[npbc_listTheory.mk_vimap_def]>>
  Induct>>rw[]>>
  xcf "fold_update_vimap_enum_arr" (get_ml_prog_state ())>>
  gvs[LIST_TYPE_def]>>
  xmatch
  >- (
    xvar>>xsimpl>>
    simp[miscTheory.enumerate_def])>>
  simp[miscTheory.enumerate_def]>>
  rpt xlet_autop>>
  xapp>>
  xsimpl
QED

(* NOTE: 100000 just a random number *)
val check_unsat' = process_topdecs `
  fun check_unsat' b fns fd lno fml pres obj fmlt prest objt =
  let
    val id = List.length fml + 1
    val arr = Array.array (2*id) None
    val arr = fill_arr arr 1 fml
    val zeros = Word8Array.array 100000 w8z
    val inds = rev_enum_full 1 fml
    val vimap = Array.array 100000 None
    val vimap = fold_update_vimap_enum_arr 1 fml vimap
    val vomap = mk_vomap_opt_arr obj
    val pc = init_conf id True pres obj
  in
    (case check_unsat'' fns fd lno arr zeros inds vimap vomap pc of
      (lno', (s, (fns',(
        (fml', (inds', pc')))))) =>
    conv_boutput_hconcl
    (get_bound pc')
    (run_concl_file fd fns' lno' s
    fml obj fml' inds'
    (get_pres pc') (get_obj pc') (get_bound pc') (get_dbound pc') (get_chk pc')
    fmlt prest objt))
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
  pres_TYPE pres presv ∧
  LIST_TYPE constraint_TYPE fmlt fmltv ∧
  obj_TYPE objt objtv ∧
  pres_TYPE prest prestv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat'" (get_ml_prog_state()))
    [bv; fnsv; fdv; lnov; fmlv; presv; objv; fmltv; prestv; objtv]
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
        sem_output (set fml) obj (pres_set_spt pres) bound (set fmlt) objt (pres_set_spt prest) output
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
  qmatch_goalsub_abbrev_tac`ARRAY cv cvs * _`>>
  `LIST_REL (OPTION_TYPE vimapn_TYPE) (REPLICATE 100000 NONE) cvs` by
    simp[Abbr`cvs`,LIST_REL_REPLICATE_same,OPTION_TYPE_def,PAIR_TYPE_def]>>
  xlet`POSTv vimapv. SEP_EXISTS vimaplsv.
    ARRAY vimapv vimaplsv * W8ARRAY v' (REPLICATE 100000 w8z) *
    ARRAY resv arrlsv' * STDIO fs *
    INSTREAM_LINES #"\n" fd fdv lines fs *
     &LIST_REL (OPTION_TYPE vimapn_TYPE)
       (mk_vimap (REPLICATE 100000 NONE) (enumerate 1 fml)) vimaplsv`
  >- (
    xapp>>xsimpl>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    simp[])>>
  rpt xlet_autop>>
  `BOOL T (Conv (SOME (TypeStamp "True" 0)) [])` by EVAL_TAC>>
  xlet_autop>>
  qmatch_asmsub_abbrev_tac`LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv`>>
  qmatch_asmsub_abbrev_tac`LIST_TYPE _ inds indsv`>>
  qmatch_asmsub_abbrev_tac`LIST_REL (OPTION_TYPE vimapn_TYPE) vimap vimaplsv`>>
  qmatch_asmsub_abbrev_tac`vomap_TYPE vomap vomapv`>>
  qmatch_goalsub_abbrev_tac`W8ARRAY zerosv zeros`>>
  `EVERY (λw. w = 0w) zeros` by
    gvs[Abbr`zeros`,w8z_def]>>
  Cases_on`
    parse_and_run fns (MAP toks_fast lines) fmlls zeros inds vimap
      vomap
      (init_conf (LENGTH fml + 1) T pres obj)`
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
        sem_output (set fml) obj (pres_set_spt pres) bound (set fmlt) objt (pres_set_spt prest) output
      | INL l => T)`
  >- (
    xlet`POSTv v.
       SEP_EXISTS k lines' lno' fmlv' fmllsv' res.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         ARRAY fmlv' fmllsv' *
         &(
          parse_and_run fns (MAP toks_fast lines)
            fmlls zeros inds vimap vomap (init_conf (LENGTH fml + 1) T pres obj) =
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
          pc'.pres pc'.obj pc'.bound pc'.dbound pc'.chk fmlt prest objt output ∧
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
      fs[get_pres_def,get_obj_def,get_bound_def,get_dbound_def,get_chk_def]>>
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
        gs[rev_enum_full_rev_enumerate]>>
        metis_tac[])>>
      simp[get_bound_def]>>
      match_mp_tac (GEN_ALL npbc_listTheory.check_csteps_list_output)>>
      first_x_assum (irule_at Any)>>
      unabbrev_all_tac>>
      gs[rev_enum_full_rev_enumerate]>>
      metis_tac[])>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  xsimpl
QED

(* TODO: We should check that the number of constraints is correct here *)
Definition check_f_line_def:
  check_f_line s =
  case strip_term_line s of NONE => F
  | SOME s =>
  case s of [] => F
  | x::xs => x = INL(strlit "f")
End

val r = translate check_f_line_def;

val headertrm = rconc (EVAL``toks_fast (strlit"pseudo-Boolean proof version 3.0")``);

Definition parse_header_line_fast_def:
  parse_header_line_fast s ⇔
  s = ^headertrm
End

val r = translate parse_header_line_fast_def;

Definition check_header_full_def:
  check_header_full s (s':(mlstring + int) list option) =
  case s of NONE => SOME 1
  | SOME s =>
  case s' of NONE => SOME 2
  | SOME s' =>
  if parse_header_line_fast s then
    if check_f_line s' then NONE
    else SOME (2:num)
  else SOME 1
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
  fun check_unsat_top b fns fml pres obj fmlt prest objt fname =
  let
    val fd = TextIO.b_openIn fname
  in
    case check_header fd of
      Some n =>
      (TextIO.b_closeIn fd;
      Inl (format_failure n "Unable to parse header"))
    | None =>
      let val res =
        (check_unsat' b fns fd 3 fml pres obj fmlt prest objt)
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
  pres_TYPE pres presv ∧
  LIST_TYPE constraint_TYPE fmlt fmltv ∧
  obj_TYPE objt objtv ∧
  pres_TYPE prest prestv ∧
  FILENAME f fv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_top"(get_ml_prog_state()))
  [bv; fnsv; fmlv; presv; objv; fmltv; prestv; objtv; fv]
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
        sem_output (set fml) obj (pres_set_spt pres) bound (set fmlt) objt (pres_set_spt prest) output
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
            sem_output (set fml) obj (pres_set_spt pres) bound (set fmlt) objt (pres_set_spt prest) output
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
val res = translate list_to_num_set_def;
val res = translate normalise_prob_def;

val res = translate mk_map_def;
val res = translate name_to_num_var_def;
val res = translate name_to_num_lit_def;
val res = translate name_to_num_lin_term_def;
val res = translate name_to_num_obj_def;
val res = translate name_to_num_pbf_def;
val res = translate name_to_num_list_def;
val res = translate name_to_num_pres_def;
val res = translate name_to_num_prob_def;

Definition hash_str_def:
  hash_str (s:mlstring) =
    let l = strlen s in
      if l = 0 then 0:num else
        l + ORD (strsub s (l-1))
End

(* not used
Definition normalise_full_def:
  normalise_full prob =
  let s = init_state hash_str compare in
  let (prob',t) = name_to_num_prob prob s in
  (normalise_prob prob', t)
End *)

val res = translate init_state_def;
val res = translate hash_str_def;

Definition normalise_full_2_def:
  normalise_full_2 prob probt =
  let s = init_state hash_str compare in
  let (prob',t) = name_to_num_prob prob s in
  let (probt',u) = name_to_num_prob probt t in
  (normalise_prob prob',
  normalise_prob probt', u)
End

val res = translate normalise_full_2_def;

Definition name_to_num_var_nf_def:
  name_to_num_var_nf v s =
  SOME (name_to_num_var v s)
End

val res = translate name_to_num_var_nf_def;

val check_unsat_top_norm = process_topdecs `
  fun check_unsat_top_norm b prob probt fname =
  case normalise_full_2 prob probt of
    ((pres,(obj,fml)),((prest,(objt,fmlt)),t)) =>
    check_unsat_top b (name_to_num_var_nf,t) fml pres obj fmlt prest objt fname
    `|> append_prog

Overload "prob_TYPE" = ``
  PAIR_TYPE
  (OPTION_TYPE
    (LIST_TYPE STRING_TYPE))
  (PAIR_TYPE
  (OPTION_TYPE
    (PAIR_TYPE
    (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE)))
    INT))
  (LIST_TYPE
    (PAIR_TYPE PBC_PBOP_TYPE
      (PAIR_TYPE
        (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE)))
        INT))))``

Theorem check_unsat_top_norm_spec:
  BOOL b bv ∧
  prob_TYPE prob probv ∧
  prob_TYPE probt probtv ∧
  FILENAME f fv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_top_norm"
    (get_ml_prog_state()))
  [bv; probv; probtv; fv]
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
         sem_concl (set (SND (SND prob))) (FST (SND prob)) concl ∧
         sem_output (set (SND (SND prob))) (FST (SND prob)) (pres_set_list (FST prob)) bound
          (set (SND (SND probt))) (FST (SND probt)) (pres_set_list (FST probt)) output
       | INL l => T))
Proof
  rw[]>>
  xcf"check_unsat_top_norm"(get_ml_prog_state()) >>
  xlet_autop>>
  `∃pres obj fml prest objt fmlt t.
    normalise_full_2 prob probt = ((pres,obj,fml),(prest,objt,fmlt),t)` by
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
  PairCases_on`prob`>>
  PairCases_on`probt`>>
  fs[normalise_full_2_def]>>
  pairarg_tac>>gvs[]>>
  pairarg_tac>>gvs[]>>
  rename1`sem_concl _ _ con ∧ sem_output _ _ _ _ _ _ _ out`>>
  PairCases_on`prob'`>>
  drule name_to_num_prob_concl_thm>>
  PairCases_on`probt'`>>
  dxrule_at_then (Pos (el 2)) drule name_to_num_prob_output_thm>>
  simp[]>>
  rename1`sem_output _ _ _ bnd _ _ _ _`>>
  disch_then(qspecl_then[`bnd`,`out`] mp_tac)>>
  impl_keep_tac
  >- (
    CONJ_ASM1_TAC >- (
      match_mp_tac init_state_ok>>
      fs[TotOrd_compare])>>
    metis_tac[name_to_num_state_ok_name_to_num_prob])>>
  simp[]>>
  metis_tac[normalise_prob_sem_concl,normalise_prob_sem_output]
QED

Overload "annot_prob_TYPE" = ``
  PAIR_TYPE
  (OPTION_TYPE
    (LIST_TYPE STRING_TYPE))
  (PAIR_TYPE
  (OPTION_TYPE
    (PAIR_TYPE
    (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE)))
    INT))
  (LIST_TYPE
    (PAIR_TYPE (OPTION_TYPE STRING_TYPE)
    ((PAIR_TYPE PBC_PBOP_TYPE
      (PAIR_TYPE
        (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE)))
        INT))))))``

val res = translate lit_string_def;
val res = translate lhs_string_def;
val res = translate op_string_def;
val res = translate pbc_string_def;
val res = translate annot_pbc_string_def;
val res = translate obj_string_def;
val res = translate pb_parseTheory.pres_string_def;
val res = translate print_prob_def;
val res = translate print_annot_prob_def;
val res = translate strip_annot_prob_def;

(* An empty formula *)
Definition default_prob_def:
  default_prob = (NONE,NONE,[]):
    mlstring list option #
    ((int # mlstring pbc$lit) list # int) option #
    (pbop # (int # mlstring pbc$lit) list # int) list
End

val res = translate default_prob_def;

Theorem all_lines_gen_all_lines[simp]:
  all_lines_gen #"\n" fs f =
  all_lines fs f
Proof
  rw[all_lines_def,all_lines_gen_def,lines_of_def,lines_of_gen_def,splitlines_at_def,splitlines_def,str_def]
QED
