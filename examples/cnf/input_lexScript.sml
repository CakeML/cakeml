(*
  The lexer for the text input formats and the DIMACS skeleton shared by
  the CNF formats, followed by scan_toks, which computes the lexer's result
  directly on a line.
*)
Theory input_lex
Ancestors
  misc mlint mlstring
Libs
  preamble

(***
  Parsing helpers for top-level formulas being read from files.
  These should be defined as cleanly as possible.
***)

(* Everything recognized as a "blank" *)
Definition blanks_def:
  blanks (c:char) ⇔ c = #" " ∨ c = #"\n" ∨ c = #"\t" ∨ c = #"\r"
End

Definition tokenize_def:
  tokenize (s:mlstring) =
  case mlint$fromString s of
    NONE => INL s
  | SOME i => INR i
End

Definition toks_def:
  toks s = MAP tokenize (tokens blanks s)
End

(* Parse ints until the next zero and returns. *)
Definition parse_until_zero_aux_def:
  (parse_until_zero_aux [] acc = NONE) ∧
  (parse_until_zero_aux (x::xs) acc =
    case x of
      INL _ => NONE
    | INR l =>
    if l = 0:int then
      SOME (REVERSE acc, xs)
    else
      parse_until_zero_aux xs (l::acc)
  )
End

Definition parse_until_zero_def:
  parse_until_zero ls =
    parse_until_zero_aux ls []
End

Theorem parse_until_zero_aux_nz:
  ∀ls acc c rest.
  parse_until_zero_aux ls acc = SOME (c,rest) ∧
  EVERY (λi. i ≠ 0) acc ⇒
  EVERY (λi. i ≠ 0) c
Proof
  Induct>>
  rw[parse_until_zero_aux_def]>>
  gvs[AllCaseEqs()]>>
  first_x_assum match_mp_tac>>
  last_x_assum (irule_at Any)>>
  simp[]
QED

Theorem parse_until_zero_nz:
  parse_until_zero ls = SOME (c,rest) ⇒
  EVERY (λi. i ≠ 0) c
Proof
  rw[parse_until_zero_def]>>
  drule parse_until_zero_aux_nz>>
  simp[]
QED

(* Lines to keep: comments start with a single "c", and blank lines
  tokenize to the empty list. *)
Definition keep_line_def:
  (keep_line (INL c::cs) ⇔ (c ≠ «c»)) ∧
  (keep_line [] ⇔ F) ∧
  (keep_line _ = T)
End

(***
  DIMACS file parsing.

  The body parser is parameterised by a line parser so that formats
  extending DIMACS (e.g. with XOR or BNN lines) reuse the same
  header handling, comment stripping and length check. Such formats
  parse each line into a sum type and partition the result.
***)

Definition parse_header_line_def:
  parse_header_line ls =
  case ls of
    [p; cnf; vars; numls] =>
    if p = INL «p» ∧ cnf = INL «cnf»
    then
      case (vars, numls)
      of
        (INR v,INR c) => if v ≥ 0 ∧ c ≥ 0 then SOME (Num v,Num c) else NONE
      | _ => NONE
    else NONE
  | _ => NONE
End

(* Produces the parsed lines in the order they are read *)
Definition parse_body_gen_def:
  (parse_body_gen pl maxvar [] acc = SOME (REVERSE acc)) ∧
  (parse_body_gen pl maxvar (s::ss) acc =
    case pl maxvar s of
      NONE => NONE
    | SOME c => parse_body_gen pl maxvar ss (c::acc)
  )
End

Theorem LENGTH_parse_body_gen:
  ∀ss pl mv acc res.
  parse_body_gen pl mv ss acc = SOME res ⇒
  LENGTH res = LENGTH ss + LENGTH acc
Proof
  Induct>>fs[parse_body_gen_def]>>
  rw[]>>every_case_tac>>fs[]>>
  first_x_assum drule>>
  simp[]
QED

(* Any property guaranteed by the line parser lifts to the whole body *)
Theorem parse_body_gen_EVERY:
  ∀ss pl mv acc res.
  parse_body_gen pl mv ss acc = SOME res ∧
  EVERY P acc ∧
  (∀s c. pl mv s = SOME c ⇒ P c) ⇒
  EVERY P res
Proof
  Induct>>fs[parse_body_gen_def]>>
  rw[]>>every_case_tac>>fs[]>>
  first_x_assum irule>>
  first_x_assum (irule_at Any)>>
  simp[]>>
  metis_tac[]
QED

(* A body parses to exactly the lines the line parser accepts *)
Theorem parse_body_gen_LIST_REL:
  ∀ss acc res.
  LIST_REL (λs c. pl mv s = SOME c) ss res ⇒
  parse_body_gen pl mv ss acc = SOME (REVERSE acc ++ res)
Proof
  Induct>>rw[parse_body_gen_def]>>
  gvs[]>>
  first_x_assum drule>>
  simp[]
QED

(* Strip comments, read the header, parse the body and check the
  declared line count. *)
Definition parse_dimacs_toks_gen_def:
  parse_dimacs_toks_gen pl tokss =
  let kept = FILTER keep_line tokss in
  case kept of
    s::ss =>
      (case parse_header_line s of
        SOME (vars,numls) =>
          if LENGTH ss = numls then
            (case parse_body_gen pl vars ss [] of
              NONE => NONE
            | SOME acc => SOME (vars,numls,acc))
          else NONE
      | NONE => NONE)
  | [] => NONE
End

(***
  scan_toks: toks computed directly on the line
***)

val _ = numLib.temp_prefer_num();

(* Generic mlstring and mlint facts, belonging upstream *)

Theorem EL_explode:
  EL n (explode s) = strsub s n
Proof
  Cases_on`s`>>simp[]
QED

Theorem strsub_implode:
  strsub (implode s) n = EL n s
Proof
  fs[strsub_def]
QED

Theorem strsub_substring:
  a < n ∧ i + n ≤ strlen s ⇒
  strsub (substring s i n) a = strsub s (i + a)
Proof
  Cases_on`s`>>
  rw[mlstringTheory.strsub_def,mlstringTheory.substring_def,
     SEG_TAKE_DROP,EL_TAKE,EL_DROP]
QED

Theorem substring_substring:
  a + b ≤ n ∧ i + n ≤ strlen s ⇒
  substring (substring s i n) a b = substring s (i + a) b
Proof
  Cases_on`s`>>
  rw[mlstringTheory.substring_def,SEG_TAKE_DROP,TAKE_TAKE,DROP_DROP,DROP_TAKE]
QED

Theorem fromChars_range_unsafe_substring:
  ∀n p len s.
  n ≤ len ∧ p + len ≤ strlen s ⇒
  fromChars_range_unsafe 0 n (substring s p len) = fromChars_range_unsafe p n s
Proof
  Induct>>
  rw[fromChars_range_unsafe_def,strsub_substring]
QED

Theorem fromChars_substring_NONE:
  p ≤ q ∧ q < p + n ∧ p + n ≤ strlen s ∧ ¬isDigit (strsub s q) ⇒
  fromChars n (substring s p n) = NONE
Proof
  strip_tac>>
  `¬IS_SOME (fromChars n (substring s p n))` suffices_by
    (Cases_on`fromChars n (substring s p n)`>>simp[])>>
  DEP_REWRITE_TAC [mlintTheory.fromChars_IS_SOME_IFF]>>
  simp[mlstringTheory.strlen_substring,TAKE_LENGTH_ID_rwt,EXISTS_MEM,MEM_EL,
       PULL_EXISTS]>>
  qexists_tac`q - p`>>
  simp[EL_explode,strsub_substring,mlstringTheory.strlen_substring]
QED

Theorem fromChars_substring_SOME:
  (∀q. p ≤ q ∧ q < p + n ⇒ isDigit (strsub s q)) ∧ 0 < n ∧ p + n ≤ strlen s ⇒
  fromChars n (substring s p n) = SOME (fromChars_range_unsafe p n s)
Proof
  strip_tac>>
  DEP_REWRITE_TAC [mlintTheory.fromChars_eq_unsafe]>>
  simp[mlstringTheory.strlen_substring,mlintTheory.fromChars_range_unsafe_eq,
       fromChars_range_unsafe_substring,EVERY_EL,EL_explode,
       strsub_substring]
QED

Theorem fromChars_range_unsafe_snoc:
  p ≤ j ⇒
  fromChars_range_unsafe p (j + 1 - p) s =
  10 * fromChars_range_unsafe p (j - p) s + (ORD (strsub s j) − 48)
Proof
  strip_tac>>
  `j + 1 - p = SUC (j - p)` by decide_tac>>
  pop_assum SUBST1_TAC>>
  REWRITE_TAC[mlintTheory.fromChars_range_unsafe_def,
              mlintTheory.fromChar_unsafe_def]>>
  simp[]
QED

Theorem fromChars_range_unsafe_1:
  fromChars_range_unsafe p 1 s = ORD (strsub s p) − 48
Proof
  REWRITE_TAC[ONE,mlintTheory.fromChars_range_unsafe_def,
              mlintTheory.fromChar_unsafe_def]>>
  simp[]
QED

(* acc extended by the digits s[j..e), as an integer, or -1 if one is not
  a digit; k counts the digits read so far, up to 9. Arithmetic is on small
  integers (mlint's smallnum functions): indices with s as the witness,
  character codes below 256, and the first nine digits of the number, whose
  value stays below 10 ** 9 < 2 ** 30; later digits use unbounded
  arithmetic. *)
Definition num_run_def:
  num_run s e (j:num) (acc:num) (k:num) =
  if smallnum_lt_str j e s then
    let oc = ORD (strsub_unsafe s j) in
    if smallnum_le 48 oc ∧ smallnum_le oc 57 then
      if smallnum_lt k 9 then
        num_run s e (smallnum_add_str j 1 s)
          (smallnum_add (smallnum_mul acc 10) (smallnum_sub oc 48))
          (smallnum_add k 1)
      else num_run s e (smallnum_add_str j 1 s) (acc * 10 + smallnum_sub oc 48) k
    else (-1:int)
  else &acc
Termination
  WF_REL_TAC`measure (λ(s,e,j,acc,k). e - j)`>>
  rw[smallnum_lt_str_def,smallnum_add_str_def]
End

Theorem num_run_thm:
  ∀s e j acc k p.
  p ≤ j ∧ j ≤ e ∧ e ≤ strlen s ∧
  acc = fromChars_range_unsafe p (j − p) s ⇒
  num_run s e j acc k =
  if ∀q. j ≤ q ∧ q < e ⇒ isDigit (strsub s q)
  then &fromChars_range_unsafe p (e − p) s
  else -1
Proof
  ho_match_mp_tac num_run_ind>>
  rpt gen_tac>>strip_tac>>
  rpt gen_tac>>strip_tac>>
  simp[Once num_run_def]>>
  fs[smallnum_lt_str_def,smallnum_add_str_def,smallnum_le_def,smallnum_lt_def,
     smallnum_add_def,smallnum_sub_def,smallnum_mul_def,
     mlstringTheory.strsub_unsafe_eq_strsub]>>
  reverse (Cases_on`j < e`)
  >- (`j = e` by decide_tac>>simp[])>>
  simp[]>>
  reverse IF_CASES_TAC
  >- (
    rw[]>>
    first_x_assum (qspec_then`j` mp_tac)>>
    simp[isDigit_def])>>
  `ORD (strsub s j) + 10 * fromChars_range_unsafe p (j − p) s − 48 =
   fromChars_range_unsafe p (j + 1 − p) s` by
    simp[fromChars_range_unsafe_snoc]>>
  `(∀q. j ≤ q ∧ q < e ⇒ isDigit (strsub s q)) ⇔
   (∀q. j + 1 ≤ q ∧ q < e ⇒ isDigit (strsub s q))` by (
    rw[EQ_IMP_THM]>>
    Cases_on`q = j`>>gvs[isDigit_def])>>
  simp[]
QED

(* Computing toks directly on the line (toks_scan_toks below): scan_toks
  skips blanks, scan_end finds where each token ends and tok_val converts it.
  Arithmetic is on small integers (mlint's smallnum functions): indices with s
  as the witness and character codes below 256. *)

(* The end of the token from j: the first blank at or after j, or n if there
  is none *)
Definition scan_end_def:
  scan_end s n (j:num) =
  if smallnum_lt_str j n s then
    let oc = ORD (strsub_unsafe s j) in
    if ¬smallnum_lt 32 oc ∧
       (smallnum_eq oc 32 ∨ smallnum_eq oc 10 ∨ smallnum_eq oc 9 ∨ smallnum_eq oc 13)
    then j
    else scan_end s n (smallnum_add_str j 1 s)
  else j
Termination
  WF_REL_TAC`measure (λ(s,n,j). n - j)`>>
  rw[smallnum_lt_str_def,smallnum_add_str_def]
End

(* TODO: move to stringTheory *)
Theorem ORD_eq_CHR[local]:
  n < 256 ⇒ (ORD c = n ⇔ c = CHR n)
Proof
  rw[EQ_IMP_THM]>>
  simp[stringTheory.CHR_ORD,stringTheory.ORD_CHR_RWT]
QED

Theorem scan_blank[local]:
  (¬(32 < ORD c) ∧
   (ORD c = 32 ∨ ORD c = 10 ∨ ORD c = 9 ∨ ORD c = 13)) ⇔ blanks c
Proof
  rw[blanks_def,ORD_eq_CHR]>>
  eq_tac>>rw[]>>
  simp[]
QED

Theorem scan_nonblank[local]:
  (32 < ORD c ∨
   ORD c ≠ 32 ∧ ORD c ≠ 10 ∧ ORD c ≠ 9 ∧ ORD c ≠ 13) ⇔ ¬blanks c
Proof
  PURE_REWRITE_TAC [GSYM scan_blank]>>
  tautLib.TAUT_TAC
QED

Theorem scan_end_ge:
  ∀s n j. j ≤ scan_end s n j
Proof
  ho_match_mp_tac scan_end_ind>>
  rw[]>>
  rw[Once scan_end_def]>>
  fs[smallnum_add_str_def]
QED

Theorem scan_end_thm:
  ∀s n j e.
  n = strlen s ∧ j ≤ n ∧ scan_end s n j = e ⇒
  j ≤ e ∧ e ≤ n ∧ (∀q. j ≤ q ∧ q < e ⇒ ¬blanks (strsub s q)) ∧
  (e < n ⇒ blanks (strsub s e))
Proof
  ho_match_mp_tac scan_end_ind>>
  rpt gen_tac>>strip_tac>>
  rpt gen_tac>>strip_tac>>
  qpat_x_assum`scan_end _ _ _ = _` mp_tac>>
  simp[Once scan_end_def]>>
  fs[smallnum_lt_str_def,smallnum_add_str_def,smallnum_eq_def,smallnum_lt_def,
     mlstringTheory.strsub_unsafe_eq_strsub,scan_blank,scan_nonblank]>>
  Cases_on`j < strlen s`>>simp[]>>
  Cases_on`blanks (strsub s j)`>>simp[]>>
  strip_tac>>
  gvs[]>>
  rw[]>>
  Cases_on`q = j`>>gvs[]
QED

(* The token s[i..e), i < e; num_run reads the digits after the first *)
Definition tok_val_def:
  tok_val s i e =
  let oc = ORD (strsub_unsafe s i) in
  let j1 = smallnum_add_str i 1 s in
  if smallnum_le 48 oc ∧ smallnum_le oc 57 then
    let v = num_run s e j1 (smallnum_sub oc 48) 1 in
    if v < 0 then INL (substring s i (smallnum_sub_str e i s)) else INR v
  else if (smallnum_eq oc 126 ∨ smallnum_eq oc 45 ∨ smallnum_eq oc 43) ∧
          smallnum_lt_str j1 e s then
    let c2 = ORD (strsub_unsafe s j1) in
    if smallnum_le 48 c2 ∧ smallnum_le c2 57 then
      let v = num_run s e (smallnum_add_str j1 1 s) (smallnum_sub c2 48) 1 in
      if v < 0 then INL (substring s i (smallnum_sub_str e i s))
      else INR (if smallnum_eq oc 43 then v else -v)
    else INL (substring s i (smallnum_sub_str e i s))
  else INL (substring s i (smallnum_sub_str e i s))
End

Theorem tok_val_thm:
  i < e ∧ e ≤ strlen s ⇒
  tok_val s i e = tokenize (substring s i (e − i))
Proof
  strip_tac>>
  simp[tok_val_def,tokenize_def,mlintTheory.fromString_def,
    mlstringTheory.strlen_substring,strsub_substring,substring_substring,
    smallnum_le_def,smallnum_eq_def,smallnum_lt_str_def,smallnum_add_str_def,
    smallnum_sub_def,smallnum_sub_str_def,mlstringTheory.strsub_unsafe_eq_strsub]>>
  Cases_on`48 ≤ ORD (strsub s i) ∧ ORD (strsub s i) ≤ 57`>>simp[]
  >- (
    `strsub s i ≠ #"~" ∧ strsub s i ≠ #"-" ∧ strsub s i ≠ #"+"` by
      (rpt strip_tac>>fs[])>>
    qspecl_then[`s`,`e`,`i + 1`,`ORD (strsub s i) − 48`,`1`,`i`] mp_tac
      num_run_thm>>
    simp[fromChars_range_unsafe_1]>>
    strip_tac>>
    Cases_on`∀q. i + 1 ≤ q ∧ q < e ⇒ isDigit (strsub s q)`>>simp[]
    >- (
      DEP_REWRITE_TAC [fromChars_substring_SOME]>>
      rw[]>>
      Cases_on`q = i`>>gvs[isDigit_def])>>
    gvs[]>>
    DEP_REWRITE_TAC [fromChars_substring_NONE]>>
    simp[]>>
    qexists_tac`q`>>
    simp[])>>
  simp[ORD_eq_CHR]>>
  Cases_on`strsub s i = #"~" ∨ strsub s i = #"-" ∨ strsub s i = #"+"`
  >- (
    reverse (Cases_on`i + 1 < e`)
    >- (
      `e = i + 1` by decide_tac>>
      gvs[mlintTheory.fromChars_def])>>
    simp[]>>
    reverse (Cases_on`48 ≤ ORD (strsub s (i + 1)) ∧ ORD (strsub s (i + 1)) ≤ 57`)
    >- (
      `fromChars (e − (i + 1)) (substring s (i + 1) (e − (i + 1))) = NONE` by (
        irule fromChars_substring_NONE>>
        simp[]>>
        qexists_tac`i + 1`>>
        fs[isDigit_def])>>
      fs[])>>
    qspecl_then[`s`,`e`,`i + 2`,`ORD (strsub s (i + 1)) − 48`,`1`,`i + 1`]
      mp_tac num_run_thm>>
    simp[fromChars_range_unsafe_1]>>
    strip_tac>>
    Cases_on`∀q. i + 2 ≤ q ∧ q < e ⇒ isDigit (strsub s q)`>>simp[]
    >- (
      `fromChars (e − (i + 1)) (substring s (i + 1) (e − (i + 1))) =
       SOME (fromChars_range_unsafe (i + 1) (e − (i + 1)) s)` by (
        irule fromChars_substring_SOME>>
        rw[]>>
        Cases_on`q = i + 1`>>gvs[isDigit_def])>>
      gvs[])>>
    `fromChars (e − (i + 1)) (substring s (i + 1) (e − (i + 1))) = NONE` by (
      irule fromChars_substring_NONE>>
      gvs[]>>
      qexists_tac`q`>>
      simp[])>>
    gvs[])>>
  `fromChars (e − i) (substring s i (e − i)) = NONE` by (
    irule fromChars_substring_NONE>>
    simp[]>>
    qexists_tac`i`>>
    simp[isDigit_def])>>
  fs[]
QED

(* The tokens of s from j *)
(* TMC *)
Definition scan_toks_def:
  scan_toks s n (j:num) =
  if smallnum_lt_str j n s then
    let oc = ORD (strsub_unsafe s j) in
    let j1 = smallnum_add_str j 1 s in
    if ¬smallnum_lt 32 oc ∧
       (smallnum_eq oc 32 ∨ smallnum_eq oc 10 ∨ smallnum_eq oc 9 ∨ smallnum_eq oc 13)
    then scan_toks s n j1
    else
      let e = scan_end s n j1 in
      let t = tok_val s j e in
        t :: scan_toks s n e
  else []
Termination
  WF_REL_TAC`measure (λ(s,n,j). n - j)`>>
  rw[smallnum_lt_str_def,smallnum_add_str_def]>>
  qspecl_then[`s`,`n`,`j + 1`] assume_tac scan_end_ge>>
  decide_tac
End

(* tokens_alt_aux reading the token s[i..e) from j onwards *)
Theorem tokens_alt_aux_tok[local]:
  ∀j. i ≤ j ∧ j ≤ e ∧ e ≤ strlen s ∧ i < e ∧
  (∀q. i ≤ q ∧ q < e ⇒ ¬blanks (strsub s q)) ∧
  (e < strlen s ⇒ blanks (strsub s e)) ⇒
  tokens_alt_aux blanks s i j (strlen s) =
  substring s i (e − i) ::
    (if e < strlen s then tokens_alt_aux blanks s (e + 1) (e + 1) (strlen s)
     else [])
Proof
  completeInduct_on`e - j`>>
  rpt strip_tac>>
  simp[Once mlstringTheory.tokens_alt_aux_def]>>
  Cases_on`j < e`
  >- (
    `j < strlen s ∧ ¬blanks (strsub s j)` by simp[]>>
    simp[]>>
    first_x_assum (qspec_then`e − (j + 1)` mp_tac)>>
    simp[]>>
    disch_then (qspecl_then[`e`,`j + 1`] mp_tac)>>
    simp[])>>
  `j = e` by decide_tac>>
  Cases_on`e < strlen s`>>gvs[]
QED

Theorem scan_toks_tokens[local]:
  ∀s n j.
  n = strlen s ∧ j ≤ n ⇒
  scan_toks s n j = MAP tokenize (tokens_alt_aux blanks s j j n)
Proof
  ho_match_mp_tac scan_toks_ind>>
  rpt gen_tac>>strip_tac>>
  rpt strip_tac>>
  simp[Once scan_toks_def,Once mlstringTheory.tokens_alt_aux_def]>>
  fs[smallnum_lt_str_def,smallnum_add_str_def,smallnum_eq_def,smallnum_lt_def,
     mlstringTheory.strsub_unsafe_eq_strsub,scan_blank,scan_nonblank]>>
  Cases_on`j < strlen s`>>simp[]>>
  Cases_on`blanks (strsub s j)`>>simp[]>>
  qabbrev_tac`e = scan_end s (strlen s) (j + 1)`>>
  qspecl_then[`s`,`strlen s`,`j + 1`,`e`] mp_tac scan_end_thm>>
  simp[]>>
  strip_tac>>
  `tok_val s j e = tokenize (substring s j (e − j))` by
    (irule tok_val_thm>>simp[])>>
  qspec_then`j + 1` mp_tac (Q.INST [`i`|->`j`] tokens_alt_aux_tok)>>
  impl_tac
  >- (
    rw[]>>
    Cases_on`q = j`>>gvs[])>>
  strip_tac>>
  `tokens_alt_aux blanks s e e (strlen s) =
   if e < strlen s then tokens_alt_aux blanks s (e + 1) (e + 1) (strlen s)
   else []` by
    (simp[Once mlstringTheory.tokens_alt_aux_def]>>rw[])>>
  simp[]
QED

Theorem toks_scan_toks:
  toks s = scan_toks s (strlen s) 0
Proof
  rw[toks_def,mlstringTheory.tokens_alt]>>
  irule (GSYM scan_toks_tokens)>>
  simp[]
QED
