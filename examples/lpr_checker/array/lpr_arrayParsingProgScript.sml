(*
  Adds a parser for LPR
*)
Theory lpr_arrayParsingProg
Ancestors
UnsafeProof lpr lpr_list lpr_parsing HashtableProof mlint
lpr_arrayProg
Libs
preamble basis

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = translation_extends"lpr_arrayProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

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

Theorem fromChars_unsafe_ind[local]:
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

val result = translate lpr_parsingTheory.fromString_unsafe_def;

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

val _ = translate blanks_def;
val _ = translate tokenize_def;

val _ = translate tokenize_fast_def;

val _ = translate toks_def;
val _ = translate parse_until_zero_def;
val _ = translate parse_until_nn_def;

val parse_until_nn_side_def = theorem "parse_until_nn_side_def"

val parse_until_nn_side = Q.prove(`
                                  !x y. parse_until_nn_side x y ⇔ T`,
                                                                   Induct>>
                                  simp[parse_until_nn_def,Once parse_until_nn_side_def]>>
                                  rw[]>>fs[]>>
                                  intLib.ARITH_TAC) |> update_precondition

val _ = translate parse_PR_hint_def;
(* val _ = translate lit_from_int_def;

val lit_from_int_side_def = fetch "-" "lit_from_int_side_def"

val lit_from_int_side = Q.prove(`
  !x. lit_from_int_side x ⇔ T`,
  rw[lit_from_int_side_def]>>
  intLib.ARITH_TAC) |> update_precondition *)

val _ = translate parse_until_k_def;
val _ = translate parse_clause_witness_def;

val _ = translate parse_lprstep_def;
val parse_lprstep_side_def = definition"parse_lprstep_side_def";

val parse_lprstep_side = Q.prove(
  `∀x. parse_lprstep_side x = T`,
                               rw[parse_lprstep_side_def] >>
    fs[integerTheory.int_ge]) |> update_precondition;

(* Uncompressed parsing *)
val parse_one_u = process_topdecs`
fun parse_one_u lno fd =
case TextIO.b_inputLineTokens #"\n" fd blanks tokenize_fast of
  None => None
| Some l =>
    case parse_lprstep l of
      None =>
        raise Fail (format_failure lno "failed to parse line (uncompressed format)")
    | Some lpr => Some lpr` |> append_prog;

val blanks_v_thm = theorem "blanks_v_thm";
val tokenize_v_thm = theorem "tokenize_v_thm";
val tokenize_fast_v_thm = theorem "tokenize_fast_v_thm";

val b_inputLineTokens_specialize =
b_inputLineTokens_spec_lines
  |> Q.GEN `f` |> Q.SPEC`blanks`
               |> Q.GEN `fv` |> Q.SPEC`blanks_v`
                             |> Q.GEN `g` |> Q.ISPEC`tokenize_fast`
                                          |> Q.GEN `gv` |> Q.ISPEC`tokenize_fast_v`
                                                        |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
                                                                     |> SIMP_RULE std_ss [blanks_v_thm,tokenize_fast_v_thm,blanks_def] ;

Definition parse_one_u_def:
  parse_one_u lines =
  case lines of [] => SOME NONE
             | (x::xs) =>
                 case parse_lprstep (toks_fast x) of NONE => NONE
                                                  | SOME l => SOME (SOME (l,xs))
End

Theorem SEP_IMP_REFL_gc:
  (p ==>> p * GC)
Proof
  xsimpl
QED

val sep_triv = metis_tac[SEP_IMP_REFL_gc,SEP_IMP_REFL,STAR_ASSOC,STAR_COMM];

Theorem parse_one_u_spec:
  NUM lno lnov
  ⇒
  app (p : 'ffi ffi_proj)
      ^(fetch_v "parse_one_u" (get_ml_prog_state()))
      [lnov; fdv]
      (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
      (POSTve
       (λv.
          SEP_EXISTS k lines' res.
                     STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
          &(parse_one_u lines ≠ NONE ∧
            OPTION_TYPE LPR_LPRSTEP_TYPE (OPTION_MAP FST (THE (parse_one_u lines))) v ∧
            (case THE (parse_one_u lines) of NONE => lines' = []
                                          | SOME res => lines' = SND res))
       )
       (λe.
          SEP_EXISTS k lines'.
                     STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
          &(Fail_exn e ∧
            parse_one_u lines = NONE
           )))
Proof
  rw[]>>
  xcf "parse_one_u" (get_ml_prog_state ())>>
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
    \\ qexists_tac ‘fs’
    \\ qexists_tac ‘fd’ \\ xsimpl \\ fs [])
  \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
  \\ xmatch \\ fs []
  \\ xcon \\ xsimpl
  \\ simp[parse_one_u_def,OPTION_TYPE_def]
  \\ sep_triv)
  \\ xlet ‘(POSTv v.
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
  \\ rw[toks_fast_def]
  \\ sep_triv)
  \\ gvs[OPTION_TYPE_def]
  \\ xmatch
  \\ xlet_autop
  \\ simp[parse_one_u_def]
  \\ Cases_on`parse_lprstep (toks_fast h)`
  \\ gvs[OPTION_TYPE_def] \\ xmatch
  >- (
  rpt xlet_autop>>
  xraise>>xsimpl>>
  gvs[Fail_exn_def]>>
  first_x_assum (irule_at Any)>>
  sep_triv)>>
  xcon>>
  xsimpl>>
  qexists_tac`k`>>
             xsimpl
QED

val res = translate parse_vb_string_aux_def;
val parse_vb_string_aux_side = Q.prove(
  `∀a b c x y z. c <= strlen a ⇒
    parse_vb_string_aux_side a b c x y z`,
                             ho_match_mp_tac parse_vb_string_aux_ind>>rw[]>>
    rw[Once (fetch "-" "parse_vb_string_aux_side_def")]>>
    fs[])
                                 |> update_precondition;

val res = translate (parse_vb_string_def |> REWRITE_RULE [GSYM sub_check_def]);
val parse_vb_string_side = Q.prove(
  `∀a. parse_vb_string_side a = T`,
                                 EVAL_TAC>>
    rw[]>>
    match_mp_tac parse_vb_string_aux_side>>
    simp[]) |> update_precondition;

val res = translate (parse_vb_string_head_def |> REWRITE_RULE [GSYM sub_check_def]);
val parse_vb_string_head_side = Q.prove(
  `∀a. parse_vb_string_head_side a = T`,
                                      EVAL_TAC>>
    rw[]>>
    match_mp_tac parse_vb_string_aux_side>>
    simp[]) |> update_precondition;

val res = translate clausify_aux_def;
val res = translate clausify_def;

val res = translate parse_vb_until_k_def;
val res = translate parse_vb_clause_witness_def;
val res = translate parse_vb_until_nn_def;

val parse_vb_until_nn_side = Q.prove(
  `∀a b.
      parse_vb_until_nn_side a b = T`,
                                    Induct>>
    rw[Once (fetch "-" "parse_vb_until_nn_side_def")]>>
    intLib.ARITH_TAC)
                               |> update_precondition;

val res = translate parse_vb_PR_hint_def;

val res = translate do_PR_def;

val do_pr_side = Q.prove(
  `∀a b.
      do_pr_side a b = T`,
                        rw[Once (fetch "-" "do_pr_side_def")]>>
    intLib.ARITH_TAC)
                   |> update_precondition;

Definition c0_def:
  c0 = CHR 0
End

val c0_v_thm = translate c0_def;

val parse_one_c = process_topdecs`
fun parse_one_c lno fd =
case TextIO.b_inputLine c0 fd of
  None => None
| Some l =>
    (case parse_vb_string_head l of
       None => raise Fail (format_failure lno "failed to parse line (compressed format)")
     | Some (Inl d) => Some d
     | Some (Inr r) =>
         (case TextIO.b_inputLine c0 fd of
            None => raise Fail (format_failure lno "failed to parse line (compressed format)")
          | Some y =>
              (case do_pr r y of
                 None => raise Fail (format_failure lno "failed to parse line (compressed format)")
               | Some p => Some p)
         )
    )` |> append_prog;

Definition parse_one_c_def:
  parse_one_c lines =
  case lines of [] => SOME NONE
             | (l::xs) =>
                 (
                 case parse_vb_string_head l of
                   NONE => NONE
                 | SOME (INL d) => SOME (SOME (d, xs))
                 | SOME (INR r) =>
                     (case xs of [] => NONE
                              | (y::ys) =>
                                  case do_PR r y of NONE => NONE
                                                 | SOME res => SOME (SOME (res, ys)))
                 )
End

Theorem parse_one_c_spec:
  NUM lno lnov
  ⇒
  app (p : 'ffi ffi_proj)
      ^(fetch_v "parse_one_c" (get_ml_prog_state()))
      [lnov; fdv]
      (STDIO fs * INSTREAM_LINES c0 fd fdv lines fs)
      (POSTve
       (λv.
          SEP_EXISTS k lines' res.
                     STDIO (forwardFD fs fd k) * INSTREAM_LINES c0 fd fdv lines' (forwardFD fs fd k) *
          &(parse_one_c lines ≠ NONE ∧
            OPTION_TYPE LPR_LPRSTEP_TYPE (OPTION_MAP FST (THE (parse_one_c lines))) v ∧
            (case THE (parse_one_c lines) of NONE => lines' = []
                                          | SOME res => lines' = SND res))
       )
       (λe.
          SEP_EXISTS k lines'.
                     STDIO (forwardFD fs fd k) * INSTREAM_LINES c0 fd fdv lines' (forwardFD fs fd k) *
          &(Fail_exn e ∧
            parse_one_c lines = NONE
           )))
Proof
  rw[]>>
  xcf "parse_one_c" (get_ml_prog_state ())>>
  xlet ‘(POSTv v.
               SEP_EXISTS k.
               STDIO (forwardFD fs fd k) *
         INSTREAM_LINES c0 fd fdv (TL lines) (forwardFD fs fd k) *
         & OPTION_TYPE STRING_TYPE (oHD lines) v)’
  >- (
  xapp>>
  simp[c0_v_thm])>>
  simp[parse_one_c_def]>>
  Cases_on`lines`>>fs[OPTION_TYPE_def]>>xmatch
  >- (
  xcon>>xsimpl>>
  sep_triv)>>
  xlet_autop>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
  xmatch>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  gvs[Fail_exn_def]>>
  first_x_assum (irule_at Any)>>
  sep_triv)>>
  TOP_CASE_TAC>>fs[SUM_TYPE_def]>>xmatch
  >- (
  xcon>>xsimpl>>
  simp[OPTION_TYPE_def]>>
  sep_triv)>>
  rename1`INSTREAM_LINES c0 fd fdv lines`>>
         xlet ‘(POSTv v.
                      SEP_EXISTS k.
                      STDIO (forwardFD fs fd k) *
                INSTREAM_LINES c0 fd fdv (TL lines) (forwardFD fs fd k) *
                & OPTION_TYPE STRING_TYPE (oHD lines) v)’
  >- (
  xapp>>
  irule_at Any c0_v_thm>>xsimpl>>
  qexists_tac`lines`>>
             qexists_tac`forwardFD fs fd k`>>
             qexists_tac`fd`>>
             xsimpl>>
  simp[forwardFD_o]>>
  sep_triv)>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (
  rpt xlet_autop>>
  xraise>>xsimpl>>
  gvs[Fail_exn_def]>>
  first_x_assum (irule_at Any)>>
  sep_triv)>>
  xlet_autop>>
  rename1`do_PR y r`>>
         Cases_on`do_PR y r`>>fs[OPTION_TYPE_def]>>xmatch
  >- (
  rpt xlet_autop>>
  xraise>>xsimpl>>
  gvs[Fail_exn_def]>>
  first_x_assum (irule_at Any)>>
  sep_triv)>>
  xcon>>xsimpl>>
  qexists_tac`k`>>
             xsimpl
QED

val parse_one = process_topdecs`
fun parse_one b lno fd =
if b
then parse_one_c lno fd
else parse_one_u lno fd` |> append_prog;

Definition parse_one_def:
  parse_one b lines =
  if b then parse_one_c lines
  else parse_one_u lines
End

Definition term_char_def:
  term_char b = (if b then c0 else #"\n")
End

Theorem parse_one_spec:
  BOOL b bv ∧
  NUM lno lnov
  ⇒
  app (p : 'ffi ffi_proj)
      ^(fetch_v "parse_one" (get_ml_prog_state()))
      [bv; lnov; fdv]
      (STDIO fs * INSTREAM_LINES (term_char b) fd fdv lines fs)
      (POSTve
       (λv.
          SEP_EXISTS k lines' res.
                     STDIO (forwardFD fs fd k) * INSTREAM_LINES (term_char b) fd fdv lines' (forwardFD fs fd k) *
          &(parse_one b lines ≠ NONE ∧
            OPTION_TYPE LPR_LPRSTEP_TYPE (OPTION_MAP FST (THE (parse_one b lines))) v ∧
            (case THE (parse_one b lines) of NONE => lines' = []
                                          | SOME res => lines' = SND res))
       )
       (λe.
          SEP_EXISTS k lines'.
                     STDIO (forwardFD fs fd k) * INSTREAM_LINES (term_char b) fd fdv lines' (forwardFD fs fd k) *
          &(Fail_exn e ∧
            parse_one b lines = NONE
           )))
Proof
  rw[]>>
  xcf "parse_one" (get_ml_prog_state ())>>
  simp[term_char_def,parse_one_def]>>xif>>
  xapp>>metis_tac[]
QED

val check_unsat'' = process_topdecs `
fun check_unsat'' b fd lno mindel fml ls carr earr =
case parse_one b lno fd of
  None => (fml,ls)
| Some lpr =>
    case check_lpr_step_arr lno mindel lpr fml ls carr earr of
      (fml',ls',carr',earr') =>
        check_unsat'' b fd (lno+1) mindel fml' ls' carr' earr'`
          |> append_prog;

Theorem parse_one_less:
  parse_one b lines = SOME (SOME (fml, rest)) ⇒
  LENGTH rest < LENGTH lines
Proof
  rw[parse_one_def,parse_one_c_def,parse_one_u_def,AllCaseEqs()]>>
  simp[]
QED

Definition parse_and_run_def:
  parse_and_run b lines mindel fml inds Clist earliest =
  case parse_one b lines of
    NONE => NONE
  | SOME NONE => SOME (fml, inds)
  | SOME (SOME (lpr,rest)) =>
      case check_lpr_step_list mindel lpr fml inds Clist earliest of
        NONE => NONE
      | SOME (fml', inds', Clist', earliest') => parse_and_run b rest mindel fml' inds' Clist' earliest'
Termination
  WF_REL_TAC`measure (LENGTH o FST o SND)`>>
            rw[]>>
  metis_tac[parse_one_less]
End

Theorem check_unsat''_spec:
  !b lines mindel fmlls ls Clist earliest
     fs fmlv fmllsv lsv Carrv lno lnov mindelv Earrv earliestv.
    BOOL b bv ∧
    NUM lno lnov ∧
    NUM mindel mindelv ∧
    (LIST_TYPE NUM) ls lsv ∧
    LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
    LIST_REL (OPTION_TYPE NUM) earliest earliestv ∧
    bounded_fml (LENGTH Clist) fmlls
    ⇒
    app (p : 'ffi ffi_proj)
        ^(fetch_v "check_unsat''" (get_ml_prog_state()))
        [bv; fdv; lnov; mindelv; fmlv; lsv; Carrv; Earrv]
        (STDIO fs * ARRAY fmlv fmllsv * W8ARRAY Carrv Clist *
         ARRAY Earrv earliestv * INSTREAM_LINES (term_char b) fd fdv lines fs)
        (POSTve
         (λv.
            SEP_EXISTS k v1 v2.
                       STDIO (forwardFD fs fd k) * INSTREAM_LINES (term_char b) fd fdv [] (forwardFD fs fd k) *
            &(v = Conv NONE [v1; v2]) *
            (SEP_EXISTS fmllsv'.
                        ARRAY v1 fmllsv' *
             &(unwrap_TYPE
               (λv fv.
                  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FST v) fv)
               (parse_and_run b lines mindel fmlls ls Clist earliest) fmllsv')) *
            &(unwrap_TYPE (λa b. LIST_TYPE NUM (SND a) b)
                          (parse_and_run b lines mindel fmlls ls Clist earliest) v2)
         )
         (λe.
            SEP_EXISTS k fmlv fmllsv Earrv earliestv lines'.
                       STDIO (forwardFD fs fd k) * INSTREAM_LINES (term_char b) fd fdv lines' (forwardFD fs fd k) *
            ARRAY fmlv fmllsv *
            ARRAY Earrv earliestv *
            &(Fail_exn e ∧ parse_and_run b lines mindel fmlls ls Clist earliest = NONE)))
Proof
  ho_match_mp_tac parse_and_run_ind>>rw[]>>
  xcf "check_unsat''" (get_ml_prog_state ())>>
  xlet`(POSTve
        (λv.
           SEP_EXISTS k lines' res.
                      STDIO (forwardFD fs fd k) * INSTREAM_LINES (term_char b) fd fdv lines' (forwardFD fs fd k) *
           ARRAY fmlv fmllsv * W8ARRAY Carrv Clist * ARRAY Earrv earliestv *
           &(parse_one b lines ≠ NONE ∧
             OPTION_TYPE LPR_LPRSTEP_TYPE (OPTION_MAP FST (THE (parse_one b lines))) v ∧
             (case THE (parse_one b lines) of NONE => lines' = []
                                           | SOME res => lines' = SND res))
        )
        (λe.
           SEP_EXISTS k lines'.
                      STDIO (forwardFD fs fd k) * INSTREAM_LINES (term_char b) fd fdv lines' (forwardFD fs fd k) *
           ARRAY fmlv fmllsv * ARRAY Earrv earliestv *
           &(Fail_exn e ∧
             parse_one b lines = NONE
            )))`
  >- (
  xapp>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  xsimpl>>
  qexists_tac`lines`>>
             qexists_tac`fs`>>
             qexists_tac`fd`>>
             qexists_tac`ARRAY fmlv fmllsv * W8ARRAY Carrv Clist * ARRAY Earrv earliestv`>>
                                                                         xsimpl>>
  rw[]
  >- (first_x_assum (irule_at Any)>> sep_triv)>>
  qexists_tac`x`>>
             qexists_tac`x'`>>
             xsimpl)
  >- (
  xsimpl>>
  simp[Once parse_and_run_def]>>
  sep_triv)>>
  simp[Once parse_and_run_def]>>
  TOP_CASE_TAC>>gvs[]>>
  TOP_CASE_TAC>>gvs[OPTION_TYPE_def]>>
  xmatch
  >- (
    xcon>>
    xsimpl
    >- (
      fs [unwrap_TYPE_def]>>
      simp[Once parse_and_run_def]>>
      qexists_tac`k`>>
      xsimpl)>>
    simp[Once parse_and_run_def])>>
  xlet_auto
  >- (
    xsimpl>>
    sep_triv)
  >- (
    xsimpl>>
    simp[Once parse_and_run_def]>>
    rw[]>> TOP_CASE_TAC>>fs[]>>
    sep_triv)>>
  xmatch>>
  xlet_autop >>
  xapp>>xsimpl>>
  fs [unwrap_TYPE_def]>>
  PairCases_on`a`>>gvs[]>>
  first_assum (irule_at Any)>>
  first_assum (irule_at Any)>>
  first_assum (irule_at Any)>>
  Cases_on`x'`>>gvs[]>>
  qexists_tac`forwardFD fs fd k`>>
  qexists_tac`emp`>>
  xsimpl>>rw[]
  >- (
    simp[Once parse_and_run_def]>>
    simp[forwardFD_o]>>
    sep_triv)>>
  simp[Once parse_and_run_def]>>
  simp[forwardFD_o]>>
  sep_triv
QED

Definition good_char_opt_def:
  (good_char_opt NONE = F) ∧
  (good_char_opt (SOME c) = good_char c)
End

val res = translate good_char_def;
val res = translate good_char_opt_def;

(* Implements the general unsat checking routine that can be called
   in several different ways
  Returns: Inl (error string)
  Otherwise: Inr (true/false result of checking clause inclusion)
*)
val check_unsat' = process_topdecs `
  fun check_unsat' mindel fml ls earr fname n cls =
  let
    val fd = TextIO.b_openIn fname
    val b = good_char_opt (TextIO.b_peekChar fd)
    val carr = Word8Array.array n w8z
    val chk = Inr (check_unsat'' b fd 0 mindel fml ls carr earr)
      handle Fail s => Inl s
    val close = TextIO.b_closeIn fd;
  in
    case chk of
      Inl s => Inl s
    | Inr res =>
      case res of (fml', ls') =>
      Inr (contains_clauses_arr fml' ls' cls)
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)` |> append_prog;

(* TODO: COPIED from readerProg, should be moved *)
Theorem fastForwardFD_ADELKEY_same[simp]:
   forwardFD fs fd n with infds updated_by ADELKEY fd =
   fs with infds updated_by ADELKEY fd
Proof
  fs [forwardFD_def, IO_fs_component_equality]
QED

Theorem parse_one_wf_lpr:
  parse_one b ls = SOME (SOME (l,r)) ⇒
  wf_lpr l
Proof
  rw[parse_one_def,parse_one_u_def,parse_one_c_def,parse_vb_string_head_def]>>
  gvs[AllCaseEqs(),wf_lpr_def]
  >-
    metis_tac[do_PR_wf_lpr]
  >-
    metis_tac[parse_lprstep_wf]
QED

Theorem parse_and_run_imp_lpr:
  ∀b ls mindel fml inds Clist earliest.
  parse_and_run b ls mindel fml inds Clist earliest = SOME (q,r) ⇒
  ∃lpr.
    EVERY wf_lpr lpr ∧
    check_lpr_list mindel lpr fml inds Clist earliest = SOME (q,r)
Proof
  ho_match_mp_tac parse_and_run_ind>>rw[]>>
  pop_assum mp_tac>> simp[Once parse_and_run_def]>>every_case_tac>>gvs[]>>rw[]
  >- (
    qexists_tac`[]`>>
    simp[check_lpr_list_def])>>
  rename1`SOME (SOME (l,_))`>>
  gvs[]>>
  qexists_tac`l::lpr`>>
  simp[check_lpr_list_def]>>
  metis_tac[parse_one_wf_lpr]
QED

Theorem check_unsat'_spec:
  NUM n nv ∧
  NUM mindel mindelv ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  LIST_REL (OPTION_TYPE NUM) earliest earliestv ∧
  (LIST_TYPE (LIST_TYPE INT)) cls clsv ∧
  FILENAME f fv ∧
  hasFreeFD fs ∧
  bounded_fml n fmlls
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat'"(get_ml_prog_state()))
  [mindelv; fmlv; lsv; Earrv; fv; nv; clsv]
  (STDIO fs * ARRAY fmlv fmllsv * ARRAY Earrv earliestv)
  (POSTv v.
    STDIO fs *
    SEP_EXISTS res.
      &(SUM_TYPE STRING_TYPE (OPTION_TYPE (LIST_TYPE INT)) res v ∧
      case res of
        INL err => T
      | INR b =>
        inFS_fname fs f ∧
        ∃lpr fml' inds'.
          EVERY wf_lpr lpr ∧
          check_lpr_list mindel lpr fmlls
            ls (REPLICATE n w8z) earliest =
            SOME (fml', inds') ∧
          b = contains_clauses_list_err fml' inds' cls
      ))
Proof
  rw[]>>
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
      STDIO fs *
      ARRAY Earrv earliestv *
      SEP_EXISTS fmllsv'. ARRAY fmlv fmllsv'`
    >-
      (xlet_auto_spec (SOME b_openIn_STDIO_spec) \\ xsimpl)
    >>
      fs[BadFileName_exn_def]>>
      xcases>>rw[]>>
      xlet_auto>>xsimpl>>
      xcon>>xsimpl>>
      qexists_tac`INL (notfound_string f)`>>simp[SUM_TYPE_def])>>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval` \\ xsimpl >>
  qunabbrev_tac`Qval`>>
  gvs[consistentFS_def]>>
  gvs[file_content_def,inFS_fname_def]>>
  `∃text. ALOOKUP fs.inode_tbl (File ino) = SOME text` by
      (gvs[ALOOKUP_EXISTS_IFF,MEM_MAP]>>
      metis_tac[FST,PAIR])>>
  xlet`POSTv is.
    STDIO (openFileFS f fs ReadMode 0) *
      INSTREAM_STR (nextFD fs) is text (openFileFS f fs ReadMode 0) *
      ARRAY fmlv fmllsv * ARRAY Earrv earliestv`
  >- (
    xapp_spec b_openIn_spec_str >>
    xsimpl>>
    rpt(first_x_assum (irule_at Any))>>
    gvs[consistentFS_def]>>
    gvs[file_content_def,inFS_fname_def]>>
    first_x_assum drule>>rw[]>>
    qexists_tac`ARRAY fmlv fmllsv * ARRAY Earrv earliestv`>>
    xsimpl)>>
  qmatch_goalsub_abbrev_tac`STDIO fss`>>
  qmatch_goalsub_abbrev_tac`INSTREAM_STR fdd`>>
  xlet`POSTv v. SEP_EXISTS k.
         STDIO (forwardFD fss fdd k) *
         INSTREAM_STR fdd is text (forwardFD fss fdd k) *
         &OPTION_TYPE CHAR (oHD text) v *
         ARRAY fmlv fmllsv * ARRAY Earrv earliestv`
  >- (
    xapp_spec b_peekChar_spec_str>>xsimpl>>
    qexists_tac`ARRAY fmlv fmllsv * ARRAY Earrv earliestv`>>
    qexists_tac`text`>>
    qexists_tac`fss`>>
    qexists_tac`fdd`>>
    xsimpl>>
    sep_triv)>>
  xlet_autop>>
  rename1`BOOL b bv`>>
  qabbrev_tac`lines = lines_of_gen (term_char b) (implode text)`>>
  xlet`POSTv warr.
    W8ARRAY warr (REPLICATE n w8z) * STDIO (forwardFD fss fdd k) *
    INSTREAM_LINES (term_char b) fdd is lines (forwardFD fss fdd k) * ARRAY fmlv fmllsv *
    ARRAY Earrv earliestv`
  >- (
    xapp>> xsimpl>>
    irule_at Any w8z_v_thm>>
    first_x_assum (irule_at Any)>>
    simp[INSTREAM_LINES_def,Abbr`lines`]>>
    xsimpl>>
    sep_triv)>>
  qmatch_goalsub_abbrev_tac`STDIO fsss`>>
  qabbrev_tac`Clist = REPLICATE n w8z`>>
  xlet`POSTv resv.
         SEP_EXISTS v0 v1 v2 fmllsv' fmlv' earliestv Earrv k rest.
          STDIO (forwardFD fsss fdd k) *
          INSTREAM_LINES (term_char b) fdd is rest (forwardFD fsss fdd k) *
          ARRAY fmlv' fmllsv' *
          &(
            case
              parse_and_run b lines mindel fmlls ls (REPLICATE n w8z) earliest
            of
              NONE => resv = Conv (SOME (TypeStamp "Inl" 4)) [v0] ∧ ∃s. STRING_TYPE s v0
            | SOME(fmlls',inds') =>
              resv = Conv (SOME (TypeStamp "Inr" 4)) [Conv NONE [v1; v2]] ∧
              v1 = fmlv' ∧
              LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls' fmllsv' ∧ LIST_TYPE NUM inds' v2
          )`
  >- (
    simp[]>>
    TOP_CASE_TAC
    >- (
      xhandle`POSTe e.
        SEP_EXISTS fmlv fmllsv rest k.
          STDIO (forwardFD fsss fdd k) *
          INSTREAM_LINES (term_char b) fdd is rest (forwardFD fsss fdd k) *
          ARRAY fmlv fmllsv *
          &(Fail_exn e ∧ parse_and_run b lines mindel fmlls ls Clist earliest = NONE)`
      >- (
        (* this used to be an xauto_let .. sigh *)
        xlet `POSTe e.
         SEP_EXISTS k fmlv fmllsv lines'.
           STDIO (forwardFD fsss fdd k) *
           INSTREAM_LINES (term_char b) fdd is lines' (forwardFD fsss fdd k) *
           ARRAY fmlv fmllsv *
           &(Fail_exn e ∧ parse_and_run b lines mindel fmlls ls Clist earliest = NONE)`
        >- (
          xapp_spec check_unsat''_spec
          \\ xsimpl
          \\ qexists_tac `emp`
          \\ rpt (first_assum (irule_at Any))
          \\ qexists_tac `lines`
          \\ qexists_tac `fsss`
          \\ qexists_tac `fdd`
          \\ xsimpl \\ fs [unwrap_TYPE_def,Abbr`Clist`]
          \\ rpt strip_tac \\ gvs[]
          \\ qexists_tac `x`
          \\ rename [`ARRAY a1 a2`]
          \\ qexists_tac `a1`
          \\ qexists_tac `a2`
          \\ rename [`INSTREAM_LINES _ _ _ xxx`]
          \\ qexists_tac `xxx`
          \\ xsimpl)>>
        fs[unwrap_TYPE_def]>>
        xsimpl>>
        rw[]>>
        rename [`ARRAY a1 a2`] >>
        qexists_tac `a1` >>
        qexists_tac `a2` >>
        xsimpl>>
        sep_triv)>>
      fs[Fail_exn_def]>>
      xcases>>
      xcon>>xsimpl>>
      simp[PULL_EXISTS]>>
      asm_exists_tac>> simp[]>>
      rename [`ARRAY a1 a2`] >>
      qexists_tac `a2` >>
      qexists_tac `a1` >>
      sep_triv)
    >>
    xhandle`(POSTv v.
        SEP_EXISTS v1 v2 k rest.
         STDIO (forwardFD fsss fdd k) *
         INSTREAM_LINES (term_char b) fdd is rest (forwardFD fsss fdd k) *
         &(v = Conv (SOME (TypeStamp "Inr" 4)) [Conv NONE [v1; v2]]) *
         (SEP_EXISTS fmllsv'.
           ARRAY v1 fmllsv' *
           &(unwrap_TYPE
             (λv fv. LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FST v) fv)
                (parse_and_run b lines mindel fmlls ls Clist earliest) fmllsv')) *
         &unwrap_TYPE (λa b. LIST_TYPE NUM (SND a) b)
           (parse_and_run b lines mindel fmlls ls Clist earliest) v2)`
    >- (
        xlet `POSTv v.
                   SEP_EXISTS k v1 v2.
                       STDIO (forwardFD fsss fdd k) *
                       INSTREAM_LINES (term_char b) fdd is [] (forwardFD fsss fdd k) *
                       &(v = Conv NONE [v1; v2]) *
                       (SEP_EXISTS fmllsv'.
                            ARRAY v1 fmllsv' *
                            &unwrap_TYPE
                              (λv fv.
                                   LIST_REL (OPTION_TYPE (LIST_TYPE INT))
                                     (FST v) fv)
                              (parse_and_run b lines mindel fmlls ls Clist earliest)
                              fmllsv') *
                       &unwrap_TYPE (λa b. LIST_TYPE NUM (SND a) b)
                         (parse_and_run b lines mindel fmlls ls Clist earliest) v2`
        >- (
          xapp_spec check_unsat''_spec
          \\ xsimpl
          \\ qexists_tac `emp`
          \\ rpt (first_assum (irule_at Any))
          \\ qexists_tac `lines`
          \\ qexists_tac `fsss`
          \\ qexists_tac `fdd`
          \\ xsimpl \\ fs [unwrap_TYPE_def,Abbr`Clist`]
          \\ rpt strip_tac \\ gvs[]
          \\ sep_triv)>>
        fs[unwrap_TYPE_def]>>
        xcon >>
        xsimpl>>
        gvs[] >> sep_triv)>>
      xsimpl>>simp[unwrap_TYPE_def]>>
      Cases_on`x`>>fs[]>>rw[]>>xsimpl >>
      sep_triv)>>
  xlet `POSTv v. STDIO fs * ARRAY fmlv' fmllsv'`
  THEN1
   (xapp_spec b_closeIn_spec_lines >>
    rename [`ARRAY a1 a2`] >>
    qexists_tac `ARRAY a1 a2` >>
    qexists_tac `rest` >>
    qexists_tac `forwardFD fsss fdd k'` >>
    qexists_tac `fdd` >>
    qexists_tac `term_char b` >>
    conj_tac THEN1
     (unabbrev_all_tac
      \\ fs [forwardFD_def]
      \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
      \\ imp_res_tac fsFFIPropsTheory.STD_streams_nextFD \\ fs []) >>
    `validFileFD fdd (forwardFD fsss fdd k').infds` by
      (unabbrev_all_tac
       \\ simp[validFileFD_forwardFD]
       \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
       \\ match_mp_tac validFileFD_nextFD \\ fs []
       \\ gvs[inFS_fname_def, consistentFS_def]
       \\ metis_tac[] )>>
    xsimpl >> rw [] >>
    imp_res_tac (DECIDE ``n<m:num ==> n <= m``) >>
    imp_res_tac fsFFIPropsTheory.nextFD_leX \\ fs [] >>
    drule fsFFIPropsTheory.openFileFS_ADELKEY_nextFD >>
    unabbrev_all_tac \\ xsimpl)>>
  pop_assum mp_tac>>every_case_tac>>rw[]>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    xcon >> xsimpl >>
    qexists_tac`INL s`>>
    simp[SUM_TYPE_def])>>
  xmatch>>
  xlet_autop>>
  xcon >> xsimpl>>
  qmatch_asmsub_abbrev_tac`OPTION_TYPE _ bbb resv`>>
  qexists_tac`INR bbb`>>
  simp[SUM_TYPE_def,Abbr`bbb`]>>
  drule parse_and_run_imp_lpr>>
  rw[]>>
  metis_tac[]
QED

Theorem abs_compute:
  ABS (i:int) = if i < 0 then -i else i
Proof
  intLib.ARITH_TAC
QED

val _ = translate abs_compute;

val _ = translate max_lit_def;

val toStdString_v_thm = translate toStdString_def;

val _ = translate print_clause_def;

(* val _ = translate spt_center_def;
val _ = translate apsnd_cons_def;
val _ = translate spt_centers_def;
val _ = translate spt_right_def;
val _ = translate spt_left_def;
val _ = translate combine_rle_def;
val _ = translate spts_to_alist_def;
val _ = translate toSortedAList_def; *)

val _ = translate print_header_line_def;

val _ = translate print_dimacs_def;

val print_dimacs_side = Q.prove(
  `∀x. print_dimacs_side x = T`,
  rw[definition"print_dimacs_side_def"]>>
  `0 ≤ 0:int` by fs[]>> drule max_lit_max_1>>
  simp[])
  |> update_precondition;

val fill_earliest = process_topdecs`
  fun fill_earliest earr n ls =
    case ls of [] => earr
    | (c::cs) =>
      fill_earliest (update_earliest_arr earr n c) (n+1) cs` |> append_prog

Theorem fill_earliest_spec:
  ∀ls lsv earliest earliestv Earrv c cv.
  NUM c cv ∧
  LIST_TYPE (LIST_TYPE INT) ls lsv ∧
  LIST_REL (OPTION_TYPE NUM) earliest earliestv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"fill_earliest"(get_ml_prog_state()))
  [Earrv; cv; lsv]
  (ARRAY Earrv earliestv)
  (POSTv resv.
  SEP_EXISTS earliestv'. ARRAY resv earliestv' *
    &(LIST_REL (OPTION_TYPE NUM) (FOLDL (λacc (i,v). update_earliest acc i v) earliest (enumerate c ls)) earliestv'))
Proof
  Induct>>rw[]>>
  xcf "fill_earliest" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,miscTheory.enumerate_def]>>
  xmatch
  >- (xvar>>xsimpl)>>
  xlet_autop >>
  xlet_autop >>
  xapp>>
  xsimpl
QED

val fill_arr = process_topdecs`
  fun fill_arr arr i ls =
    case ls of [] => arr
    | (v::vs) =>
      fill_arr (Array.updateResize arr None i (Some v)) (i+1) vs` |> append_prog

Theorem fill_arr_spec:
  ∀ls lsv arrv arrls arrlsv i iv.
  NUM i iv ∧
  LIST_TYPE (LIST_TYPE INT) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) arrls arrlsv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"fill_arr"(get_ml_prog_state()))
  [arrv; iv; lsv]
  (ARRAY arrv arrlsv)
  (POSTv resv.
  SEP_EXISTS arrlsv'. ARRAY resv arrlsv' *
    & LIST_REL (OPTION_TYPE (LIST_TYPE INT))
    (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i) arrls (enumerate i ls)) arrlsv')
Proof
  Induct>>rw[]>>
  xcf "fill_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,miscTheory.enumerate_def]>>
  xmatch
  >- (xvar>>xsimpl)>>
  rpt xlet_autop >>
  simp[] >> xlet_auto>>
  xapp>>fs[]>>
  match_mp_tac LIST_REL_update_resize>>fs[]>>
  simp[OPTION_TYPE_def]
QED

Theorem all_distinct_map_fst_rev:
  ALL_DISTINCT (MAP FST ls) ⇔ ALL_DISTINCT (MAP FST (REVERSE ls))
Proof
  fs[MAP_REVERSE]
QED

Theorem LENGTH_FOLDR_update_resize1:
  ∀ll.
  LENGTH (FOLDR (λx acc. (λ(i,v). update_resize acc NONE (SOME v) i) x) (REPLICATE n NONE) ll) ≥ n
Proof
  Induct>>simp[FORALL_PROD]>>rw[]>>
  rw[Once update_resize_def]
QED

Theorem LENGTH_FOLDR_update_resize2:
  ∀ll x.
  MEM x ll ⇒
  FST x < LENGTH (FOLDR (λx acc. (λ(i,v). update_resize acc NONE (SOME v) i) x) (REPLICATE n NONE) ll)
Proof
  Induct>>simp[FORALL_PROD]>>rw[]>>
  rw[Once update_resize_def]
  >- (
    first_x_assum drule>>
    simp[])>>
  first_x_assum drule>>simp[]
QED

Theorem FOLDL_update_resize_lookup:
  ∀ls.
  ALL_DISTINCT (MAP FST ls) ⇒
  ∀x.
  x < LENGTH (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i) (REPLICATE n NONE) ls)
  ⇒
  EL x (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i) (REPLICATE n NONE) ls)
  =
  ALOOKUP ls x
Proof
  simp[Once (GSYM EVERY_REVERSE), Once (GSYM MAP_REVERSE)]>>
  simp[FOLDL_FOLDR_REVERSE]>>
  simp[GSYM alookup_distinct_reverse]>>
  simp[Once all_distinct_map_fst_rev]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE ls`>>
  pop_assum kall_tac>>
  Induct_on`ll`>-
    simp[EL_REPLICATE]>>
  simp[FORALL_PROD]>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once update_resize_def]>>
  strip_tac>>
  simp[Once update_resize_def]>>
  IF_CASES_TAC>>fs[]
  >-
    (simp[EL_LUPDATE]>>
    IF_CASES_TAC>>simp[])>>
  simp[EL_LUPDATE]>>
  IF_CASES_TAC >> simp[]>>
  simp[EL_APPEND_EQN]>>rw[]>>
  simp[EL_REPLICATE]>>
  CCONTR_TAC>>fs[]>>
  Cases_on`ALOOKUP ll x`>>fs[]>>
  drule ALOOKUP_MEM>>
  strip_tac>>
  drule LENGTH_FOLDR_update_resize2>>
  simp[]>>
  metis_tac[]
QED

Theorem any_el_update_earliest:
  ∀cl ls x y.
  index y = x ⇒
  any_el x (update_earliest ls v cl) NONE =
  case any_el x ls NONE of
    NONE => if MEM y cl then SOME v else NONE
  | SOME k =>
    if MEM y cl then SOME (MIN k v) else SOME k
Proof
  Induct>>simp[update_earliest_def]
  >-
    (rw[]>>TOP_CASE_TAC>>simp[])>>
  rw[]>>
  qmatch_goalsub_abbrev_tac`any_el _ (update_earliest lss _ _) _`>>
  simp[]
  >- (
    first_x_assum(qspecl_then[`lss`,`index h`,`h`] mp_tac)>>
    simp[Abbr`lss`,any_el_update_resize]>>
    strip_tac>>
    IF_CASES_TAC>>simp[]>>
    Cases_on`any_el (index h) ls NONE`>>simp[min_opt_def,MIN_DEF])
  >- (
    first_x_assum(qspecl_then[`lss`,`index y`,`y`] mp_tac)>>
    simp[Abbr`lss`,any_el_update_resize]>>
    strip_tac>>
    IF_CASES_TAC>>simp[]>>
    Cases_on`any_el (index h) ls NONE`>>simp[min_opt_def,MIN_DEF])>>
  fs[]>>
  first_x_assum(qspecl_then[`lss`,`y`] mp_tac)>>
  simp[Abbr`lss`,any_el_update_resize]>>
  `index y ≠ index h` by fs[index_11]>>
  simp[]
QED

Theorem SORTED_REVERSE:
  transitive P ⇒
  (SORTED P (REVERSE ls) ⇔ SORTED (λx y. P y x)  ls)
Proof
  rw[]>>
  DEP_REWRITE_TAC [SORTED_EL_LESS]>>
  fs[]>>
  CONJ_TAC>- (
    fs[transitive_def]>>
    metis_tac[])>>
  simp[EL_REVERSE]>>
  rw[EQ_IMP_THM]
  >- (
    first_x_assum (qspecl_then [`LENGTH ls-n-1`,`LENGTH ls-m-1`] mp_tac)>>
    simp[GSYM ADD1])>>
  first_x_assum match_mp_tac>>
  simp[]>>
  intLib.ARITH_TAC
QED

Theorem fml_rel_FOLDL_update_resize:
  fml_rel (build_fml k fml)
  (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i) (REPLICATE n NONE) (enumerate k fml))
Proof
  rw[fml_rel_def]>>
  simp[any_el_ALT]>>
  reverse IF_CASES_TAC
  >- (
    fs[lookup_build_fml]>>
    CCONTR_TAC>>fs[]>>
    `MEM x (MAP FST (enumerate k fml))` by
      (fs[MAP_FST_enumerate,MEM_GENLIST]>>
      intLib.ARITH_TAC)>>
    fs[MEM_MAP]>>
    fs[FOLDL_FOLDR_REVERSE]>>
    `MEM y (REVERSE (enumerate k fml))` by
      fs[MEM_REVERSE]>>
    drule LENGTH_FOLDR_update_resize2>>
    simp[]>>
    metis_tac[]) >>
  DEP_REWRITE_TAC [FOLDL_update_resize_lookup]>>
  simp[]>>
  CONJ_TAC >-
    simp[ALL_DISTINCT_MAP_FST_enumerate]>>
  simp[lookup_build_fml,ALOOKUP_enumerate]
QED

Theorem ind_rel_FOLDL_update_resize:
  ind_rel
  (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i) (REPLICATE n NONE) (enumerate k fml))
  (REVERSE (MAP FST (enumerate k fml)))
Proof
  simp[ind_rel_def,FOLDL_FOLDR_REVERSE]>>
  `∀z. MEM z (MAP FST (enumerate k fml)) ⇔ MEM z (MAP FST (REVERSE (enumerate k fml)))` by
    simp[MEM_MAP]>>
  simp[]>>
  qmatch_goalsub_abbrev_tac`MAP FST ls`>>
  rpt(pop_assum kall_tac)>>
  Induct_on`ls`>>rw[]
  >-
    metis_tac[EL_REPLICATE]>>
  Cases_on`h`>>fs[]>>
  fs[IS_SOME_EXISTS]>>
  pop_assum mp_tac>>
  simp[Once update_resize_def]>>
  pop_assum mp_tac>>
  simp[Once update_resize_def]>>
  IF_CASES_TAC>>fs[]
  >-
    (simp[EL_LUPDATE]>>
    strip_tac>>
    IF_CASES_TAC>>simp[])
  >>
  simp[EL_LUPDATE]>>
  IF_CASES_TAC>>simp[EL_APPEND_EQN]>>
  IF_CASES_TAC>>simp[]>>
  simp[EL_REPLICATE]
QED

Theorem earliest_rel_FOLDL_update_resize:
  earliest_rel
  (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i) (REPLICATE n NONE) (enumerate k fml))
  (FOLDL (λacc (i,v). update_earliest acc i v) (REPLICATE bnd NONE) (enumerate k fml))
Proof
  simp[FOLDL_FOLDR_REVERSE]>>
  qpat_abbrev_tac`lss = REVERSE _`>>
  pop_assum kall_tac>> Induct_on`lss`
  >- (
    fs[earliest_rel_def]>>rw[]>>
    TOP_CASE_TAC>>simp[EL_REPLICATE])>>
  simp[]>>strip_tac>>pairarg_tac>>simp[]>>
  metis_tac[earliest_rel_update_resize0,earliest_rel_update_resize1,earliest_rel_update_resize2]
QED

Theorem check_lpr_unsat_list_sound:
  check_lpr_unsat_list lpr
    (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i) (REPLICATE n NONE) (enumerate k fml))
    (REVERSE (MAP FST (enumerate k fml)))
    Clist
    (FOLDL (λacc (i,v). update_earliest acc i v) (REPLICATE bnd NONE) (enumerate k fml)) ∧
  EVERY wf_clause fml ∧ EVERY wf_lpr lpr ∧ EVERY ($= w8z) Clist ⇒
  unsatisfiable (interp fml)
Proof
  rw[check_lpr_unsat_list_def]>>
  every_case_tac>>fs[]>>
  assume_tac (fml_rel_FOLDL_update_resize |> INST_TYPE [alpha |-> ``:int list``])>>
  assume_tac (ind_rel_FOLDL_update_resize |> INST_TYPE [alpha |-> ``:int list``])>>
  assume_tac earliest_rel_FOLDL_update_resize>>
  drule fml_rel_check_lpr_list>>
  `SORTED $>= (REVERSE (MAP FST (enumerate k fml)))` by
    (DEP_REWRITE_TAC [SORTED_REVERSE]>>
    simp[transitive_def,MAP_FST_enumerate]>>
    match_mp_tac SORTED_weaken>>
    qexists_tac `$<`>>simp[]>>
    metis_tac[SORTED_GENLIST_PLUS])>>
  drule wf_fml_build_fml>> disch_then (qspec_then`k` assume_tac)>>
  rpt(disch_then drule)>>
  strip_tac>>
  match_mp_tac (check_lpr_unsat_sound |> SIMP_RULE std_ss [AND_IMP_INTRO] |> GEN_ALL)>>
  simp[check_lpr_unsat_def]>>
  asm_exists_tac>>simp[]>>
  qexists_tac`k`>>simp[]>>
  metis_tac[fml_rel_contains_clauses_list]
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

Theorem fml_rel_check_lpr_list:
  ∀steps mindel fml fmlls inds fmlls' inds' Clist earliest.
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  SORTED $>= inds ∧
  EVERY ($= w8z) Clist ∧ wf_fml fml ∧
  earliest_rel fmlls earliest ∧
  EVERY wf_lpr steps ∧
  check_lpr_list mindel steps fmlls inds Clist earliest = SOME (fmlls', inds') ⇒
  ind_rel fmlls' inds' ∧
  ∃fml'. check_lpr mindel steps fml = SOME fml' ∧
    fml_rel fml' fmlls'
Proof
  Induct>>fs[check_lpr_list_def,check_lpr_def]>>
  ntac 9 strip_tac>>
  ntac 4 (TOP_CASE_TAC>>fs[])>>
  strip_tac>>
  drule  fml_rel_check_lpr_step_list>>
  rpt (disch_then drule)>>
  disch_then (qspecl_then [`h`,`mindel`] mp_tac)>> simp[]>>
  strip_tac>>
  simp[]>>
  first_x_assum match_mp_tac>>
  asm_exists_tac>>fs[]>>
  asm_exists_tac>>fs[]>>
  asm_exists_tac>>fs[]>>
  qexists_tac`r`>>fs[]>>
  match_mp_tac check_lpr_step_wf_fml>>
  metis_tac[]
QED

Theorem check_lpr_sat_equiv_list_sound:
  check_lpr_sat_equiv_list lpr
    (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i) (REPLICATE n NONE) (enumerate k fml))
    (REVERSE (MAP FST (enumerate k fml)))
    Clist
    (FOLDL (λacc (i,v). update_earliest acc i v) (REPLICATE bnd NONE) (enumerate k fml))
    0 fml2 ∧
  EVERY wf_clause fml ∧ EVERY wf_lpr lpr ∧ EVERY ($= w8z) Clist ⇒
  satisfiable (interp fml) ⇒
  satisfiable (interp fml2)
Proof
  rw[check_lpr_sat_equiv_list_def]>>
  every_case_tac>>fs[]>>
  assume_tac (fml_rel_FOLDL_update_resize |> INST_TYPE [alpha |-> ``:int list``])>>
  assume_tac (ind_rel_FOLDL_update_resize |> INST_TYPE [alpha |-> ``:int list``])>>
  assume_tac earliest_rel_FOLDL_update_resize>>
  drule fml_rel_check_lpr_list>>
  `SORTED $>= (REVERSE (MAP FST (enumerate k fml)))` by
    (DEP_REWRITE_TAC [SORTED_REVERSE]>>
    simp[transitive_def,MAP_FST_enumerate]>>
    match_mp_tac SORTED_weaken>>
    qexists_tac `$<`>>simp[]>>
    metis_tac[SORTED_GENLIST_PLUS])>>
  drule wf_fml_build_fml>>
  disch_then (qspec_then`k` assume_tac)>>
  simp[]>>
  rpt(disch_then drule)>>
  strip_tac>>
  match_mp_tac (check_lpr_sat_equiv_fml |> SIMP_RULE std_ss [AND_IMP_INTRO] |> GEN_ALL)>>
  simp[check_lpr_sat_equiv_def]>>
  asm_exists_tac>>simp[]>>
  asm_exists_tac>>simp[]>>
  qexists_tac`0`>>simp[]>>
  qexists_tac`k`>>simp[]>>
  metis_tac[fml_rel_contains_clauses_list]
QED

Theorem check_lpr_range_list_sound:
  check_lpr_range_list
    lpr
    (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i) (REPLICATE n NONE) (enumerate k fml))
    (REVERSE (MAP FST (enumerate k fml)))
    (FOLDL (λacc (i,v). update_earliest acc i v) (REPLICATE bnd NONE) (enumerate k fml))
    m (LENGTH fml + k) pf i j ∧
  EVERY wf_clause fml ∧ EVERY wf_lpr lpr ∧ EVERY wf_proof pf ⇒
  satisfiable (interp (run_proof fml (TAKE i pf))) ⇒
  satisfiable (interp (run_proof fml (TAKE j pf)))
Proof
  rw[]>>
  drule fml_rel_check_lpr_range_list>>
  assume_tac (fml_rel_FOLDL_update_resize |> INST_TYPE [alpha |-> ``:int list``])>>
  disch_then drule>>
  assume_tac (ind_rel_FOLDL_update_resize |> INST_TYPE [alpha |-> ``:int list``])>>
  assume_tac earliest_rel_FOLDL_update_resize>>
  simp[]>>
  impl_tac >-(
    simp[wf_fml_build_fml]>>
    simp[transitive_def,MAP_FST_enumerate]>>
    CONJ_TAC>-(
      `ALL_DISTINCT (MAP FST (enumerate k fml))` by
        fs[ALL_DISTINCT_MAP_FST_enumerate]>>
      drule FOLDL_update_resize_lookup>>
      simp[any_el_ALT]>>
      rw[]>>
      pop_assum mp_tac>>IF_CASES_TAC>>simp[]>>
      first_x_assum(qspecl_then [`n`,`x`] mp_tac)>>
      simp[]>>
      simp[ALOOKUP_enumerate]>>
      every_case_tac>>fs[])>>
    DEP_REWRITE_TAC [SORTED_REVERSE]>>
    simp[transitive_def,MAP_FST_enumerate]>>
    match_mp_tac SORTED_weaken>>
    qexists_tac `$<`>>simp[]>>
    metis_tac[SORTED_GENLIST_PLUS])>>
  strip_tac>>
  drule check_lpr_range_sound>>
  disch_then match_mp_tac>>
  asm_exists_tac>>simp[]>>
  simp[Once CONJ_COMM]>>
  asm_exists_tac>>simp[]>>
  simp[Once CONJ_COMM]>>
  asm_exists_tac>>simp[]
QED

