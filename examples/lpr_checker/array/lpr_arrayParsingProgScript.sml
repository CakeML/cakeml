(*
  Adds a parser for LPR
*)
open preamble basis UnsafeProofTheory lprTheory lpr_listTheory lpr_parsingTheory HashtableProofTheory mlintTheory lpr_arrayProgTheory;

val _ = new_theory "lpr_arrayParsingProg"

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = translation_extends"lpr_arrayProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

(* TODO: Mostly copied from mlintTheory *)
val result = translate fromChar_unsafe_def;

Definition fromChars_range_unsafe_tail_def:
  fromChars_range_unsafe_tail b n str mul acc =
  if n ≤ b then acc
  else
    let m = sub_nocheck n 1 in
    fromChars_range_unsafe_tail b m str (mul * 10)
      (acc + fromChar_unsafe (strsub str m) * mul)
Termination
  WF_REL_TAC`measure (λ(b,n,_). n)`>>
  rw[sub_nocheck_def]
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
  simp[Once fromChars_range_unsafe_tail_def,ADD1,fromChars_range_unsafe_def,sub_nocheck_def]>>
  fs[ADD1]
QED

Theorem fromChars_range_unsafe_alt:
  fromChars_range_unsafe l n s =
  fromChars_range_unsafe_tail l (n+l) s 1 0
Proof
  rw[fromChars_range_unsafe_tail_eq]
QED

val result = translate fromChars_range_unsafe_tail_def;
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

val result = translate lpr_parsingTheory.fromString_unsafe_def;

val fromstring_unsafe_side_def = definition"fromstring_unsafe_side_def";
val fromchars_unsafe_side_def = theorem"fromchars_unsafe_side_def";
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
  simp[sub_nocheck_def]>>eq_tac>>rw[ADD1]>>
  gvs[]
QED

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

val tokenize_fast_side = Q.prove(
  `∀x. tokenize_fast_side x = T`,
  EVAL_TAC >> fs[]) |> update_precondition;

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

val res = translate parse_vb_string_aux_def;
val parse_vb_string_aux_side = Q.prove(
  `∀a b c x y z. c <= strlen a ⇒
  parse_vb_string_aux_side a b c x y z`,
  ho_match_mp_tac parse_vb_string_aux_ind>>rw[]>>
  rw[Once (fetch "-" "parse_vb_string_aux_side_def")]>>
  fs[])
  |> update_precondition;

val res = translate parse_vb_string_def;
val parse_vb_string_side = Q.prove(
  `∀a. parse_vb_string_side a = T`,
  EVAL_TAC>>
  rw[]>>
  match_mp_tac parse_vb_string_aux_side>>
  simp[]) |> update_precondition;

val res = translate parse_vb_string_head_def;
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

(* Uncompressed parsing *)
val parse_one_u = process_topdecs`
  fun parse_one_u lno fd =
  case TextIO.b_inputLineTokens fd blanks tokenize_fast of
    None => None
  | Some l =>
    case parse_lprstep l of
      None =>
      raise Fail (format_failure lno "failed to parse line (uncompressed format) ")
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
    OPTION_MAP SOME (parse_lprstep (toks_fast x))
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
    (STDIO fs * INSTREAM_LINES fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' res.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(parse_one_u lines ≠ NONE ∧
           OPTION_TYPE LPR_LPRSTEP_TYPE (THE (parse_one_u lines)) v ∧
           (THE (parse_one_u lines) ≠ NONE ⇒ LENGTH lines' < LENGTH lines))
      )
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧
            parse_one_u lines = NONE
           )))
Proof
  xcf "parse_one_u" (get_ml_prog_state ())>>
  Cases_on`lines`
  >- (
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
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs [])
    \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
    \\ xmatch \\ fs []
    \\ xcon \\ xsimpl
    \\ simp[parse_one_u_def,OPTION_TYPE_def]
    \\ sep_triv)
  \\ xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES fd fdv t (forwardFD fs fd k) *
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
    sep_triv)>>
  xcon>>
  xsimpl>>
  qexists_tac`k`>>
  qexists_tac`t`>>
  xsimpl
QED

(* TODO: COPIED -- perhaps an interface like this would work? *)
Definition compress_def:
  compress chrs = mlstring$implode (REVERSE chrs)
End

val _ = translate compress_def;

val _ = (append_prog o process_topdecs)`
  fun b_inputLine_aux c0 is k chrs strs =
    case TextIO.b_input1 is of
      None =>
        if List.null chrs andalso List.null strs
        then None
        else Some (String.concat (List.rev (compress (c0::chrs) :: strs)))
    | Some c =>
        if c = c0
        then Some (String.concat (List.rev (compress (c::chrs) :: strs)))
        else if k = 0
             then b_inputLine_aux c0 is 500 [] (compress (c::chrs) :: strs)
             else b_inputLine_aux c0 is (k-1) (c::chrs) strs`;

val _ = (append_prog o process_topdecs)`
  fun b_inputLine c0 is = b_inputLine_aux c0 is 500 [] []`;

val c0_def = Define`
  c0 = CHR 0`

val _ = translate c0_def;

val parse_one_c = process_topdecs`
  fun parse_one_c lno fd =
  let val l = TextIO.b_inputUntil fd c0
    val u = print l in
  if l = "" then None
  else
    (case parse_vb_string_head l of
      None => raise Fail (format_failure lno "failed to parse line (compressed format) ")
    | Some (Inl d) => Some d
    | Some (Inr r) =>
      (let val y = TextIO.b_inputUntil fd c0
          val u = print y in
          (case do_pr r y of
            None => raise Fail (format_failure lno "failed to parse line (compressed format) ")
          | Some p => Some p)
       end))
  end` |> append_prog;

val parse_one = process_topdecs`
  fun parse_one b lno fd =
  if b
  then parse_one_c lno fd
  else parse_one_u lno fd` |> append_prog;

val check_unsat'' = process_topdecs `
  fun check_unsat'' b fd lno mindel fml ls carr earr =
    case parse_one b lno fd of
      None => (fml,ls)
    | Some lpr =>
    case check_lpr_step_arr lno mindel lpr fml ls carr earr of
      (fml',ls',carr',earr') =>
    check_unsat'' b fd (lno+1) mindel fml' ls' carr' earr'`
    |> append_prog;

(*
(* This says what happens to the STDIO *)
val check_unsat''_def = Define`
  (check_unsat'' fd mindel fml inds Clist earliest fs [] = STDIO (fastForwardFD fs fd)) ∧
  (check_unsat'' fd mindel fml inds Clist earliest fs (ln::ls) =
    case parse_and_run_list mindel fml inds Clist earliest (toks_fast ln) of
      NONE => STDIO (lineForwardFD fs fd)
    | SOME (fml', inds', Clist', earliest') =>
      check_unsat'' fd mindel fml' inds' Clist' earliest' (lineForwardFD fs fd) ls)`

(* This says what happens to fml, inds *)
val parse_and_run_file_list_def = Define`
  (parse_and_run_file_list [] mindel fml inds Clist earliest = SOME (fml, inds)) ∧
  (parse_and_run_file_list (x::xs) mindel fml inds Clist earliest =
    case parse_and_run_list mindel fml inds Clist earliest (toks_fast x) of
      NONE => NONE
    | SOME (fml', inds', Clist', earliest') => parse_and_run_file_list xs mindel fml' inds' Clist' earliest')`

Theorem parse_and_run_file_list_eq:
  ∀ls mindel fml inds Clist earliest.
  parse_and_run_file_list ls mindel fml inds Clist earliest =
  case parse_lpr ls of
    NONE => NONE
  | SOME lpr => check_lpr_list mindel lpr fml inds Clist earliest
Proof
  Induct>>fs[parse_and_run_list_def,parse_lpr_def,parse_and_run_file_list_def,check_lpr_list_def]>>
  rw[]>>
  every_case_tac>>fs[toks_fast_def]>>
  simp[check_lpr_list_def]
QED

Theorem linesFD_cons:
  lineFD fs fd = SOME x ⇒
  linesFD fs fd = x::linesFD (lineForwardFD fs fd) fd
Proof
  Cases_on`linesFD fs fd`>>
  fs[linesFD_nil_lineFD_NONE]>>
  drule linesFD_cons_imp>>
  fs[]
QED

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

Theorem check_unsat''_spec:
  !fd fdv lines fs fmlv fmlls fmllsv ls lsv Clist Carrv lno lnov mindel mindelv Earrv earliest earliestv.
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  LIST_REL (OPTION_TYPE NUM) earliest earliestv ∧
  bounded_fml (LENGTH Clist) fmlls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat''" (get_ml_prog_state()))
    [fdv; lnov; mindelv; fmlv; lsv; Carrv; Earrv]
    (STDIO fs * ARRAY fmlv fmllsv * W8ARRAY Carrv Clist * ARRAY Earrv earliestv * INSTREAM_LINES fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k v1 v2.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv [] (forwardFD fs fd k) *
           &(v = Conv NONE [v1; v2]) *
           (SEP_EXISTS fmllsv'.
            ARRAY v1 fmllsv' *
            &(unwrap_TYPE
              (λv fv.
              LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FST v) fv)
                 (parse_and_run_file_list lines mindel fmlls ls Clist earliest) fmllsv')) *
          &(unwrap_TYPE (λa b. LIST_TYPE NUM (SND a) b)
            (parse_and_run_file_list lines mindel fmlls ls Clist earliest) v2)
      )
      (λe.
         SEP_EXISTS k fmlv fmllsv Earrv earliestv lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           ARRAY fmlv fmllsv *
           ARRAY Earrv earliestv *
           &(Fail_exn e ∧ parse_and_run_file_list lines mindel fmlls ls Clist earliest = NONE)))
Proof
  ntac 2 strip_tac
  \\ Induct \\ rw []
  \\ xcf "check_unsat''" (get_ml_prog_state ())
  THEN1 (
    xlet ‘(POSTv v.
            SEP_EXISTS k.
                ARRAY fmlv fmllsv * W8ARRAY Carrv Clist * ARRAY Earrv earliestv *
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES fd fdv [] (forwardFD fs fd k) *
                &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac ‘ARRAY fmlv fmllsv * W8ARRAY Carrv Clist * ARRAY Earrv earliestv’
      \\ qexists_tac ‘[]’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
      \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
      \\ fs[OPTION_TYPE_def])
    \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
    \\ xmatch \\ fs []
    \\ xcon \\ xsimpl
    \\ fs [parse_and_run_file_list_def]
    \\ qexists_tac ‘k’ \\ xsimpl
    \\ fs [unwrap_TYPE_def])
  \\ xlet ‘(POSTv v.
            SEP_EXISTS k.
                ARRAY fmlv fmllsv * W8ARRAY Carrv Clist * ARRAY Earrv earliestv *
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES fd fdv lines (forwardFD fs fd k) *
                & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks_fast h)) v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac ‘ARRAY fmlv fmllsv * W8ARRAY Carrv Clist * ARRAY Earrv earliestv ’
      \\ qexists_tac ‘h::lines’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
      \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
      \\ simp[toks_fast_def])
  \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
  \\ xmatch \\ fs []
  \\ xlet_auto >- (
    xsimpl>>simp[unwrap_TYPE_def]>>rw[]>>
    qexists_tac`x`>> qexists_tac`x'`>>xsimpl)
  >- (
    xsimpl>>
    simp[parse_and_run_file_list_def]>>
    xsimpl>>
    rw[]>>
    qexists_tac ‘k’>>
    qexists_tac`fmlv`>>qexists_tac`fmllsv`>>
    xsimpl>>
    qexists_tac`x`>>qexists_tac`x'`>>
    qexists_tac ‘lines’>>
    xsimpl>>
    metis_tac[])>>
  rveq \\ fs [] >>
  xmatch>>
  xlet_autop >>
  xapp>>xsimpl>>
  fs [unwrap_TYPE_def]>>
  goal_assum (first_assum o mp_then (Pos (el 2)) mp_tac)>>simp[]>>
  rfs []>> rveq \\ fs [] >>
  asm_exists_tac \\ fs []>>
  qexists_tac ‘emp’>>
  asm_exists_tac \\ fs []>>
  asm_exists_tac \\ fs []>>
  asm_exists_tac \\ fs []>>
  qexists_tac ‘(forwardFD fs fd k)’>> xsimpl>>
  simp[parse_and_run_file_list_def]>>
  PairCases_on ‘a’ \\ fs [] >>
  rveq \\ fs []>>
  rw[]>>fs[] >>
  qexists_tac ‘k+x’ \\ fs [GSYM fsFFIPropsTheory.forwardFD_o] >> xsimpl >>
  qexists_tac`x'`>>
  qexists_tac`x''` >>
  qexists_tac ‘x'''’ \\ xsimpl >>
  qexists_tac ‘x'''''’ \\ xsimpl >>
  metis_tac[]
QED

(* We don't really care about the STDIO afterwards long as it gets closed *)
Theorem check_unsat''_eq:
∀ls fd mindel fml inds fs Clist earliest.
∃n.
  check_unsat'' fd mindel fml inds Clist earliest fs ls =
  case parse_and_run_file_list ls mindel fml inds Clist earliest of
   NONE => STDIO (forwardFD fs fd n)
 | SOME _ => STDIO (fastForwardFD fs fd)
Proof
  Induct>>rw[check_unsat''_def,parse_and_run_file_list_def]>>
  TOP_CASE_TAC
  >-
    metis_tac[lineForwardFD_forwardFD]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  first_x_assum(qspecl_then[`fd`,`mindel`,`q`,`q'`,`lineForwardFD fs fd`,`q''`,`r`] strip_assume_tac)>>
  simp[]>>
  TOP_CASE_TAC>>fs[]>>
  qspecl_then [`fs`,`fd`] strip_assume_tac lineForwardFD_forwardFD>>
  simp[forwardFD_o]>>
  metis_tac[]
QED
*)

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
    val carr = Word8Array.array n w8z
    val b = good_char_opt (TextIO.b_peekChar fd)
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
          check_lpr_list mindel lpr fmlls
            ls (REPLICATE n w8z) earliest =
            SOME (fml', inds') ∧
          b = contains_clauses_list_err fml' inds' cls
      ))
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
      simp[SUM_TYPE_def]>>metis_tac[])>>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval` \\ xsimpl >>
  qunabbrev_tac`Qval`>>
  xlet_auto_spec (SOME b_openIn_spec_lines) \\ xsimpl >>
  `WORD8 w8z w8z_v` by fs[w8z_v_thm]>>
  xlet_autop >>
  qmatch_goalsub_abbrev_tac`STDIO fss`>>
  qabbrev_tac`Clist = REPLICATE n w8z`>>
  xlet`POSTv resv.
         SEP_EXISTS v0 v1 v2 fmllsv' fmlv' earliestv Earrv k rest.
          STDIO (forwardFD fss (nextFD fs) k) *
          INSTREAM_LINES (nextFD fs) is rest (forwardFD fss (nextFD fs) k) *
          ARRAY fmlv' fmllsv' *
          &(
            case
              parse_and_run_file_list (all_lines fs f) mindel fmlls ls (REPLICATE n w8z) earliest
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
          STDIO (forwardFD fss (nextFD fs) k) *
          INSTREAM_LINES (nextFD fs) is rest (forwardFD fss (nextFD fs) k) *
          ARRAY fmlv fmllsv *
          &(Fail_exn e ∧ parse_and_run_file_list (all_lines fs f) mindel fmlls ls Clist earliest = NONE)`
      >- (
        (* this used to be an xauto_let .. sigh *)
        xlet `POSTe e.
         SEP_EXISTS k fmlv fmllsv lines'.
           STDIO (forwardFD fss (nextFD fs) k) *
           INSTREAM_LINES (nextFD fs) is lines' (forwardFD fss (nextFD fs) k) *
           ARRAY fmlv fmllsv *
           &(Fail_exn e ∧ parse_and_run_file_list (all_lines fs f) mindel fmlls ls Clist earliest = NONE)`
        THEN1
         (xapp_spec check_unsat''_spec
          \\ xsimpl
          \\ qexists_tac `emp`
          \\ xsimpl \\ fs [Abbr`Clist`]
          \\ asm_exists_tac \\ fs []
          \\ asm_exists_tac \\ fs []
          \\ asm_exists_tac \\ fs []
          \\ asm_exists_tac \\ fs []
          \\ qexists_tac `all_lines fs f`
          \\ qexists_tac `fss`
          \\ qexists_tac `nextFD fs`
          \\ xsimpl \\ fs [unwrap_TYPE_def]
          \\ rpt strip_tac
          \\ qexists_tac `x`
          \\ rename [`ARRAY a1 a2`]
          \\ qexists_tac `a1`
          \\ qexists_tac `a2`
          \\ qexists_tac `x'''''`
          \\ xsimpl)>>
        fs[unwrap_TYPE_def]>>
        xsimpl>>
        rw[]>>
        rename [`ARRAY a1 a2`] >>
        qexists_tac `a1` >>
        qexists_tac `a2` >>
        xsimpl>>
        qexists_tac `x'''` >>
        qexists_tac `x` >> xsimpl) >>
      fs[Fail_exn_def]>>
      xcases>>
      xcon>>xsimpl>>
      simp[PULL_EXISTS]>>
      asm_exists_tac>> simp[]>>
      rename [`ARRAY a1 a2`] >>
      qexists_tac `a2` >>
      qexists_tac `a1` >>
      qexists_tac `k` >>
      qexists_tac `rest` >> xsimpl)
    >>
    xhandle`(POSTv v.
        SEP_EXISTS v1 v2 k rest.
         STDIO (forwardFD fss (nextFD fs) k) *
         INSTREAM_LINES (nextFD fs) is rest (forwardFD fss (nextFD fs) k) *
         &(v = Conv (SOME (TypeStamp "Inr" 4)) [Conv NONE [v1; v2]]) *
         (SEP_EXISTS fmllsv'.
           ARRAY v1 fmllsv' *
           &(unwrap_TYPE
             (λv fv. LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FST v) fv)
                (parse_and_run_file_list (all_lines fs f) mindel fmlls ls Clist earliest) fmllsv')) *
         &unwrap_TYPE (λa b. LIST_TYPE NUM (SND a) b)
           (parse_and_run_file_list (all_lines fs f) mindel fmlls ls Clist earliest) v2)`
    >- (
        xlet `POSTv v.
                   SEP_EXISTS k v1 v2.
                       STDIO (forwardFD fss (nextFD fs) k) *
                       INSTREAM_LINES (nextFD fs) is [] (forwardFD fss (nextFD fs) k) *
                       &(v = Conv NONE [v1; v2]) *
                       (SEP_EXISTS fmllsv'.
                            ARRAY v1 fmllsv' *
                            &unwrap_TYPE
                              (λv fv.
                                   LIST_REL (OPTION_TYPE (LIST_TYPE INT))
                                     (FST v) fv)
                              (parse_and_run_file_list (all_lines fs f) mindel fmlls ls Clist earliest)
                              fmllsv') *
                       &unwrap_TYPE (λa b. LIST_TYPE NUM (SND a) b)
                         (parse_and_run_file_list (all_lines fs f) mindel fmlls ls Clist earliest) v2`
        THEN1
         (xapp_spec check_unsat''_spec
          \\ xsimpl \\ qexists_tac `emp`
          \\ xsimpl \\ fs [Abbr`Clist`]
          \\ asm_exists_tac \\ fs []
          \\ asm_exists_tac \\ fs []
          \\ asm_exists_tac \\ fs []
          \\ asm_exists_tac \\ fs []
          \\ qexists_tac `all_lines fs f`
          \\ qexists_tac `fss`
          \\ qexists_tac `nextFD fs`
          \\ xsimpl \\ fs [unwrap_TYPE_def]
          \\ rpt strip_tac
          \\ qexists_tac `x'`
          \\ xsimpl) >>
        fs[unwrap_TYPE_def]>>
        xcon >>
        xsimpl>>
        rename [`forwardFD _ _ k`] \\ qexists_tac `k` >>
        rename [`INSTREAM_LINES _ _ rr`] \\ qexists_tac `rr` \\ xsimpl) >>
      xsimpl>>simp[unwrap_TYPE_def]>>
      Cases_on`x`>>fs[]>>rw[]>>xsimpl >>
      rename [`forwardFD _ _ k`] \\ qexists_tac `k` >>
      rename [`INSTREAM_LINES _ _ rr`] \\ qexists_tac `rr` \\ xsimpl)>>
  qspecl_then [`all_lines fs f`,`mindel`,`fmlls`,`ls`,`Clist`,`earliest`] strip_assume_tac parse_and_run_file_list_eq>>
  fs[]>>rw[]>>
  pop_assum kall_tac >>
  xlet `POSTv v. STDIO fs * ARRAY fmlv' fmllsv'`
  THEN1
   (xapp_spec b_closeIn_spec_lines >>
    rename [`ARRAY a1 a2`] >>
    qexists_tac `ARRAY a1 a2` >>
    qexists_tac `rest` >>
    qexists_tac `forwardFD fss (nextFD fs) k` >>
    qexists_tac `nextFD fs` >>
    conj_tac THEN1
     (fs [forwardFD_def,Abbr`fss`]
      \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
      \\ imp_res_tac fsFFIPropsTheory.STD_streams_nextFD \\ fs []) >>
    `validFileFD (nextFD fs) (forwardFD fss (nextFD fs) k).infds` by
      (simp[validFileFD_forwardFD]>> simp[Abbr`fss`]
       \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
       \\ match_mp_tac validFileFD_nextFD \\ fs []) >>
    xsimpl >> rw [] >>
    imp_res_tac (DECIDE ``n<m:num ==> n <= m``) >>
    imp_res_tac fsFFIPropsTheory.nextFD_leX \\ fs [] >>
    drule fsFFIPropsTheory.openFileFS_ADELKEY_nextFD >>
    fs [Abbr`fss`] \\ xsimpl) >>
  Cases_on`parse_lpr (all_lines fs f)`>> fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xcon >> xsimpl >>
    simp[SUM_TYPE_def]>>metis_tac[])>>
  TOP_CASE_TAC>> fs[]
  >- (
    xmatch >> xcon >>
    xsimpl>> simp[SUM_TYPE_def] >> metis_tac[])>>
  TOP_CASE_TAC>>fs[]>>
  xmatch >> fs[]>>
  xmatch >> fs[]>>
  xlet_autop>>
  xcon >> xsimpl>>
  simp[SUM_TYPE_def] *)
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
  xlet_auto>>
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

val _ = export_theory();
