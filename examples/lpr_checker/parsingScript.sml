(*
   Parsing interface for DIMACS and LPR
*)
open preamble miscTheory lprTheory mlintTheory;

val _ = new_theory "parsing";

(*
  Parses a list of strings (1 per line of a file) in DIMACS format
*)

(* Everything recognized as a "blank" *)
val blanks_def = Define`
  blanks (c:char) ⇔ c = #" " ∨ c = #"\n" ∨ c = #"\t" ∨ c = #"\r"`

val tokenize_def = Define`
  tokenize (s:mlstring) =
  case mlint$fromString s of
    NONE => INL s
  | SOME i => INR i`

val fromString_unsafe_def = Define`
  fromString_unsafe str =
    if strlen str = 0
    then 0i
    else if strsub str 0 = #"~" ∨
            strsub str 0 = #"-"
      then ~&fromChars_unsafe (strlen str - 1)
                              (substring str 1 (strlen str - 1))
      else &fromChars_unsafe (strlen str) str`;

val tokenize_fast_def = Define`
  tokenize_fast (s:mlstring) =
  if strlen s = 0 then INL s
  else if strsub s 0 = #"c" ∨ strsub s 0 = #"d" then INL s
  else INR (fromString_unsafe s)`

val toks_def = Define`
  toks s = MAP tokenize (tokens blanks s)`

val toks_fast_def = Define`
  toks_fast s = MAP tokenize_fast (tokens blanks s)`

(* DIMACS parser *)

(*
  A clause line must end with 0, cannot contain 0s elsewhere, and is within the var bound
*)
val parse_clause_aux_def = Define`
  (parse_clause_aux maxvar [] (acc:cclause) = NONE) ∧
  (parse_clause_aux maxvar [c] acc = if c = INR 0i then SOME acc else NONE) ∧
  (parse_clause_aux maxvar (x::xs) acc =
    case x of
      INR l =>
      if l = 0 ∨ Num (ABS l) > maxvar then NONE
      else parse_clause_aux maxvar xs (l::acc)
    | INL (_:mlstring) => NONE
  )`

val parse_clause_def = Define`
  parse_clause maxvar xs =
  case parse_clause_aux maxvar xs [] of
    NONE => NONE
  | SOME ls => SOME (REVERSE ls)`

Theorem parse_clause_aux_wf_clause:
  ∀mv ls acc acc'.
  wf_clause acc ∧
  parse_clause_aux mv ls acc = SOME acc' ⇒
  wf_clause acc'
Proof
  ho_match_mp_tac (fetch "-" "parse_clause_aux_ind")>>
  rw[parse_clause_aux_def]>>fs[wf_clause_def]>>
  every_case_tac>>fs[]
QED

Theorem parse_clause_wf_clause:
  parse_clause mv ls = SOME ls' ⇒
  wf_clause ls'
Proof
  simp[parse_clause_def]>>every_case_tac>>rw[]>>
  imp_res_tac parse_clause_aux_wf_clause>>
  fs[wf_clause_def]
QED

Theorem parse_clause_aux_bound:
  ∀mv ls acc acc'.
  EVERY (λi. Num (ABS i) <= mv) acc ∧
  parse_clause_aux mv ls acc = SOME acc' ⇒
  EVERY (λi. Num (ABS i) <= mv) acc'
Proof
  ho_match_mp_tac (fetch "-" "parse_clause_aux_ind")>>
  rw[parse_clause_aux_def]>>
  every_case_tac>>fs[]
QED

Theorem parse_clause_bound:
  parse_clause mv ls = SOME ls' ⇒
  EVERY (λi. Num (ABS i) <= mv) ls'
Proof
  simp[parse_clause_def]>>every_case_tac>>rw[]>>
  imp_res_tac parse_clause_aux_bound>>
  fs[EVERY_REVERSE]
QED

(* Printing a parsed clause back *)
val toStdString_def = Define`
  toStdString i =
    if 0i ≤ i ∧ i < 10 then
      str (toChar (Num (ABS i)))
    else
      implode ((if i < 0i then "-" else "")++
               (toChars (Num (ABS i) MOD maxSmall_DEC) (Num (ABS i) DIV maxSmall_DEC) ""))`;

val print_clause_def = Define`
  (print_clause [] = strlit "0\n") ∧
  (print_clause (x::xs) =
    toStdString x ^ strlit(" ") ^ print_clause xs)`

Theorem tokens_unchanged:
  EVERY ($~ o P) (explode ls) ∧ ¬ NULL (explode ls) ⇒
  tokens P ls = [ls]
Proof
  rw[] >> drule TOKENS_unchanged>>
  simp[]>>
  simp[GSYM mlstringTheory.TOKENS_eq_tokens]
QED

(* TODO: Copied from mlintTheory *)
Theorem toStdString_thm:
   toStdString i = implode ((if i < 0i then "-" else "") ++ num_to_dec_string (Num (ABS i)))
Proof
  rw[toStdString_def]
  >- (`F` by intLib.COOPER_TAC)
  >- (
    rw[mlstringTheory.str_def]
    \\ AP_TERM_TAC
    \\ `Num (ABS i) < 10` by intLib.COOPER_TAC
    \\ simp[toChar_HEX]
    \\ simp[ASCIInumbersTheory.num_to_dec_string_def]
    \\ simp[ASCIInumbersTheory.n2s_def]
    \\ simp[Once numposrepTheory.n2l_def])
  \\ (
    AP_TERM_TAC \\ simp[]
    \\ `0 < maxSmall_DEC` by EVAL_TAC
    \\ simp[toChars_thm]
    \\ qspec_then`maxSmall_DEC`mp_tac DIVISION
    \\ simp[] )
QED

Theorem fromString_toStdString[simp]:
   !i:int. fromString (toStdString i) = SOME i
Proof
  rw [toStdString_thm, mlstringTheory.implode_def]
  \\ qmatch_goalsub_abbrev_tac `strlit sss`
  \\ qspec_then `sss` mp_tac fromString_thm
  THEN1
   (reverse impl_tac THEN1
     (fs [Abbr`sss`,toString_thm,ASCIInumbersTheory.toNum_toString]
      \\ rw [] \\ last_x_assum mp_tac \\ intLib.COOPER_TAC)
    \\ fs [Abbr `sss`,EVERY_isDigit_num_to_dec_string])
  \\ `HD sss ≠ #"~" ∧ HD sss ≠ #"-" ∧ HD sss ≠ #"+"` by
   (fs [Abbr `sss`]
    \\ qspec_then `Num (ABS i)` mp_tac EVERY_isDigit_num_to_dec_string
    \\ Cases_on `num_to_dec_string (Num (ABS i))`
    \\ fs []
    \\ CCONTR_TAC \\ fs [] \\ rveq  \\ fs [isDigit_def])
  \\ fs [Abbr `sss`,EVERY_isDigit_num_to_dec_string]
  \\ fs [toString_thm,ASCIInumbersTheory.toNum_toString]
  \\ rw [] \\ last_x_assum mp_tac \\ intLib.COOPER_TAC
QED

Theorem tokens_blanks_toStdString:
  tokens blanks (toStdString h) = [toStdString h]
Proof
  match_mp_tac tokens_unchanged>>
  rw[toStdString_thm]
  >- EVAL_TAC
  >- (
    `EVERY isDigit (num_to_dec_string(Num(ABS h)))` by fs[ASCIInumbersTheory.EVERY_isDigit_num_to_dec_string]>>
    pop_assum mp_tac >> match_mp_tac MONO_EVERY>>
    EVAL_TAC>>rw[])
  >- (
    `EVERY isDigit (num_to_dec_string(Num(ABS h)))` by fs[ASCIInumbersTheory.EVERY_isDigit_num_to_dec_string]>>
    pop_assum mp_tac >> match_mp_tac MONO_EVERY>>
    EVAL_TAC>>rw[])
  >>
  Cases_on`num_to_dec_string(Num(ABS h))`>>fs[]
QED

Theorem tokens_print_clause_nonempty:
  ∀ys. tokens blanks (print_clause ys) ≠ []
Proof
  Induct>>fs[print_clause_def]
  >-
    EVAL_TAC
  >>
  `blanks #" " ∧ str #" " = strlit " "` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]
QED

Theorem parse_clause_aux_print_clause:
  ∀ys maxvar acc.
  EVERY (λl. Num (ABS l) ≤ maxvar) ys ∧
  wf_clause ys
  ⇒
  parse_clause_aux maxvar (toks (print_clause ys)) acc = SOME (REVERSE ys ++ acc)
Proof
  simp[toks_def]>>
  Induct>>rw[print_clause_def]
  >-
    EVAL_TAC
  >>
  `blanks #" " ∧ str #" " = strlit " "` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  disch_then kall_tac>>
  simp[tokens_blanks_toStdString]>>
  simp[tokenize_def]>>
  Cases_on`tokens blanks (print_clause ys)`
  >-
    fs[tokens_print_clause_nonempty]
  >>
  simp[parse_clause_aux_def]>>
  fs[wf_clause_def]
QED

Theorem parse_clause_print_clause:
  ∀ys maxvar.
  EVERY (λl. Num (ABS l) ≤ maxvar) ys ∧
  wf_clause ys
  ⇒
  parse_clause maxvar (toks (print_clause ys)) = SOME ys
Proof
  rw[parse_clause_def]>>
  drule parse_clause_aux_print_clause>>
  disch_then drule>>
  disch_then (qspec_then`[]` assume_tac)>>simp[]
QED

val parse_header_line_def = Define`
  parse_header_line ls =
  case ls of
    [p; cnf; vars; numcls] =>
    if p = INL (strlit "p") ∧ cnf = INL (strlit "cnf")
    then
      case (vars, numcls)
      of
        (INR v,INR c) => if v ≥ 0 ∧ c ≥ 0 then SOME (Num v,Num c) else NONE
      | _ => NONE
    else NONE
  | _ => NONE`

val print_header_line_def = Define`
  print_header_line v len =
  strlit ("p cnf ") ^  toStdString (&v) ^ strlit(" ") ^ toStdString (&len) ^ strlit("\n")`

Theorem parse_header_line_print_header_line:
  parse_header_line (toks (print_header_line v len)) = SOME(v,len)
Proof
  rw[print_header_line_def, toks_def]>>
  qmatch_goalsub_abbrev_tac`aa ^ bb ^ _ ^ cc ^ dd`>>
  `blanks #" " ∧ str #" " = strlit " "` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  `aa = strlit"p" ^ strlit" " ^ strlit"cnf" ^ strlit" "` by
    (fs[Abbr`aa`]>>EVAL_TAC)>>
  strip_tac>>
  first_assum(qspecl_then[`aa ^ bb`,`cc ^ dd`] assume_tac)>>fs[]>>
  `cc ^ dd = cc ^ dd ^ strlit""` by EVAL_TAC>>
  pop_assum SUBST_ALL_TAC>>
  `blanks #"\n" ∧ str #"\n" = strlit "\n"` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  unabbrev_all_tac>>
  simp[tokens_blanks_toStdString]>>
  rw[]>>
  `tokens blanks (strlit "p") = [strlit "p"]` by EVAL_TAC>>
  `tokens blanks (strlit "cnf") = [strlit "cnf"]` by EVAL_TAC>>
  `tokens blanks (strlit "") = []` by EVAL_TAC>>
  simp[tokenize_def,parse_header_line_def]>>
  EVAL_TAC>>
  simp[integerTheory.INT_POS, integerTheory.INT_GE_CALCULATE]
QED

(*
  Parse a file as DIMACS
*)

(* lines which are not comments don't start with a single "c" *)
val nocomment_line_def = Define`
  (nocomment_line (INL c::cs) = (c ≠ strlit "c")) ∧
  (nocomment_line _ = T)`

(* Produces the list of clauses in order they are read *)
val parse_dimacs_body_def = Define`
  (parse_dimacs_body maxvar [] acc = SOME (REVERSE acc)) ∧
  (parse_dimacs_body maxvar (s::ss) acc =
    case parse_clause maxvar s of
      NONE => NONE
    | SOME cl => parse_dimacs_body maxvar ss (cl::acc)
  )`

Theorem LENGTH_parse_dimacs_body:
  ∀ss mv acc res.
  parse_dimacs_body mv ss acc = SOME res ⇒
  LENGTH res = LENGTH ss + LENGTH acc
Proof
  Induct>>fs[parse_dimacs_body_def]>>
  rw[]>>every_case_tac>>fs[]>>
  first_x_assum drule>>
  simp[]
QED

(* Parse the tokenized DIMACS file as a list of clauses *)
val parse_dimacs_toks_def = Define`
  parse_dimacs_toks tokss =
  let nocomments = FILTER nocomment_line tokss in
  case nocomments of
    s::ss =>
      (case parse_header_line s of
      SOME (vars,clauses) =>
         if LENGTH ss = clauses then
          case parse_dimacs_body vars ss []
            of NONE => NONE
          | SOME acc => SOME (vars,clauses,acc)
        else NONE
      | NONE => NONE)
  | [] => NONE`

(* Parse a list of strings in DIMACS format and return a ccnf *)
val parse_dimacs_def = Define`
  parse_dimacs strs =
  let tokss = MAP toks strs in
  case parse_dimacs_toks tokss of
    NONE => NONE
  | SOME (nvars, nclauses, ls) => SOME ls`

Theorem parse_dimacs_body_wf:
  ∀ss vars acc acc'.
  parse_dimacs_body vars ss acc = SOME acc' ∧
  EVERY wf_clause acc ⇒
  EVERY wf_clause acc'
Proof
  Induct>>rw[parse_dimacs_body_def]>>
  every_case_tac>>fs[EVERY_REVERSE]>>
  first_x_assum drule>>simp[]>>
  metis_tac[parse_clause_wf_clause]
QED

Theorem parse_dimacs_body_bound:
  ∀ss vars acc acc'.
  parse_dimacs_body vars ss acc = SOME acc' ∧
  EVERY (EVERY (λi. Num (ABS i) <= vars)) acc ⇒
  EVERY (EVERY (λi. Num (ABS i) <= vars)) acc'
Proof
  Induct>>rw[parse_dimacs_body_def]>>
  every_case_tac>>fs[EVERY_REVERSE]>>
  first_x_assum drule>>simp[]>>
  disch_then match_mp_tac>>
  rw[EVERY_MEM]>>
  drule parse_clause_bound>>
  fs[EVERY_MEM]
QED

Theorem parse_dimacs_wf:
  parse_dimacs strs = SOME fml ⇒
  EVERY wf_clause fml
Proof
  simp[parse_dimacs_def,parse_dimacs_toks_def]>>
  every_case_tac>>fs[]>>
  rw[]>>
  match_mp_tac parse_dimacs_body_wf>>
  asm_exists_tac>>simp[]
QED

val max_lit_def = Define`
  (max_lit k [] = k) ∧
  (max_lit k (x::xs) = if k < ABS x then max_lit (ABS x) xs else max_lit k xs)`

val print_dimacs_def = Define`
  print_dimacs fml =
  let len = LENGTH fml in
  let v = max_lit 0 (MAP (max_lit 0) fml) in
  print_header_line (Num v) len ::
  MAP print_clause fml`

Theorem FILTER_print_clause:
  FILTER nocomment_line
    (MAP toks (MAP print_clause ls)) =
    (MAP toks (MAP print_clause ls))
Proof
  simp[FILTER_EQ_ID,EVERY_MAP,EVERY_MEM]>>
  rw[]>>
  Cases_on`x`>>simp[print_clause_def]
  >- EVAL_TAC >>
  `blanks #" " ∧ str #" " = strlit " "` by EVAL_TAC>>
  simp[toks_def]>>
  drule mlstringTheory.tokens_append>>simp[]>>
  simp[tokens_blanks_toStdString,tokenize_def,nocomment_line_def]
QED

Theorem parse_dimacs_body_MAP_print_clause:
  ∀vs acc.
  EVERY (λc. EVERY (λl. Num (ABS l) ≤ mv) c) vs ∧
  EVERY wf_clause vs
  ⇒
  parse_dimacs_body mv (MAP toks (MAP print_clause vs)) acc = SOME (REVERSE acc ++ vs)
Proof
  Induct>>rw[parse_dimacs_body_def]>>
  drule parse_clause_print_clause>> rw[]
QED

Theorem print_header_line_first:
  ∃ls. tokens blanks (print_header_line a b) =
  strlit"p"::ls
Proof
  rw[print_header_line_def]>>
  qmatch_goalsub_abbrev_tac`aa ^ bb ^ _ ^ dd ^ ee`>>
  `aa = strlit"p" ^ strlit" " ^ strlit"cnf" ^ strlit" "` by
    (fs[Abbr`aa`]>>EVAL_TAC)>>
  simp[]>>
  PURE_REWRITE_TAC[GSYM mlstringTheory.strcat_assoc]>>
  PURE_REWRITE_TAC[Once mlstringTheory.strcat_assoc]>>
  `blanks #" " ∧ str #" " = strlit " "` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  `tokens blanks (strlit "p") = [strlit "p"]` by EVAL_TAC>>
  simp[]
QED

Theorem max_lit_max_1:
  ∀ls k.
  0 ≤ k ⇒
  k ≤ max_lit k ls ∧
  (∀x. MEM x ls ⇒ ABS x ≤ max_lit k ls)
Proof
  Induct>>rw[max_lit_def]>>
  qmatch_goalsub_abbrev_tac`max_lit aa`>>
  first_x_assum(qspec_then`aa` mp_tac)>>
  simp[Abbr`aa`]>>
  rw[] >>
  intLib.COOPER_TAC
QED

Theorem max_lit_max:
  (∀x. MEM x ls ⇒ ABS x ≤ max_lit 0 ls)
Proof
  `0 ≤ 0:int` by fs[]>>
  metis_tac[max_lit_max_1]
QED

Theorem max_lit_max_lit_max:
  EVERY (λc. EVERY (λl. Num (ABS l) ≤ Num (max_lit 0 (MAP (max_lit 0) vs))) c) vs
Proof
  rw[EVERY_MEM]>>
  drule max_lit_max>>
  strip_tac>>
  `MEM (max_lit 0 c) (MAP (max_lit 0) vs)` by
    (fs[MEM_MAP]>>metis_tac[])>>
  drule max_lit_max>>
  rw[]>>
  intLib.ARITH_TAC
QED

Theorem parse_dimacs_body_length:
  ∀ss acc cls.
  parse_dimacs_body mv ss acc = SOME cls ⇒
  LENGTH cls = LENGTH ss + LENGTH acc
Proof
  Induct>>rw[parse_dimacs_body_def]>>
  every_case_tac>>fs[]>>
  first_x_assum drule>>
  simp[]
QED

Theorem parse_dimacs_toks_print_dimacs_toks:
  EVERY wf_clause fml ⇒
  ∃mv cl.
  parse_dimacs_toks (MAP toks (print_dimacs fml)) = SOME (mv,cl,fml)
Proof
  strip_tac>>simp[parse_dimacs_toks_def,print_dimacs_def]>>
  qmatch_goalsub_abbrev_tac`print_header_line a b`>>
  simp[Once toks_def]>>
  assume_tac print_header_line_first>>fs[]>>
  pop_assum sym_sub_tac>>
  `tokenize (strlit "p") = INL (strlit "p")` by EVAL_TAC>>
  simp[nocomment_line_def]>>
  simp[parse_header_line_print_header_line]>>
  unabbrev_all_tac>>
  simp[FILTER_print_clause]>>
  qmatch_goalsub_abbrev_tac`parse_dimacs_body a b c`>>
  qspecl_then [`a`,`fml`,`[]`] mp_tac (GEN_ALL parse_dimacs_body_MAP_print_clause)>>
  simp[]>>
  impl_tac >- (
    simp[]>>
    fs[Abbr`a`,max_lit_max_lit_max])>>
  simp[]
QED

Theorem parse_dimacs_print_dimacs:
  EVERY wf_clause fml ⇒
  parse_dimacs (print_dimacs fml) = SOME fml
Proof
  rw[]>>
  simp[parse_dimacs_def]>>
  mp_tac parse_dimacs_toks_print_dimacs_toks>>
  rw[]>> simp[]
QED

(* Parse a LPR clause with witness *)
(* val fromString_unsafe_def = Define`
  fromString_unsafe str =
    if strlen str = 0
    then 0i
    else if strsub str 0 = #"-"
      then ~&fromChars_unsafe (strlen str - 1)
                              (substring str 1 (strlen str - 1))
      else &fromChars_unsafe (strlen str) str`; *)

(* Parse everything until the next non-positive and returns it *)
val parse_until_nn_def = Define`
  (parse_until_nn [] acc = NONE) ∧
  (parse_until_nn (x::xs) acc =
    case x of
      INL _ => NONE
    | INR l =>
    if l ≤ 0:int then
      SOME (Num (-l), REVERSE acc, xs)
    else
      parse_until_nn xs (Num l::acc)
  )`

val parse_until_nn_length = Q.prove(`
  ∀ls acc a b c.
  parse_until_nn ls acc = SOME(a,b,c) ⇒
  LENGTH c < LENGTH ls`,
  Induct>>fs[parse_until_nn_def]>>
  rw[]>>every_case_tac>>fs[]>>
  first_x_assum drule>>
  fs[]
QED

(* Gets the rest of the witness *)
val parse_until_zero_def = Define`
  (parse_until_zero [] acc = NONE) ∧
  (parse_until_zero (x::xs) acc =
    case x of
      INL _ => NONE
    | INR l =>
    if l = 0:int then
      SOME (REVERSE acc, xs)
    else
      parse_until_zero xs (l::acc)
  )`

val parse_until_k_def = Define`
  (parse_until_k k [] acc = NONE) ∧
  (parse_until_k k (x::xs) acc =
    case x of
      INL _ => NONE
    | INR l =>
    if l = 0 then
      SOME (REVERSE acc, NONE, xs)
    else if l = k then
      case parse_until_zero xs [] of
        NONE => NONE
      | SOME (w ,rest) =>
        SOME (REVERSE acc, SOME (k::w), rest)
    else
      parse_until_k k xs (l::acc))`

val parse_clause_witness_def = Define`
  (parse_clause_witness [] = NONE) ∧
  (parse_clause_witness (x::xs) =
    case x of
      INL _ => NONE
    | INR l =>
    if l = 0:int then
      SOME ([], NONE , xs)
    else
      parse_until_k l xs [l])`

Theorem parse_until_k_wf:
  ∀ls k acc xs opt res.
  parse_until_k k ls acc = SOME(xs, opt, res) ∧
  wf_clause acc ==>
  wf_clause xs ∧
  (case opt of SOME w => MEM k w | NONE => T) ∧
  ∃front. xs = REVERSE acc ++ front
Proof
  Induct>>simp[parse_until_k_def]>>
  ntac 6 strip_tac>>
  TOP_CASE_TAC>>
  IF_CASES_TAC
  >-
    (rw[]>>fs[wf_clause_def])>>
  reverse IF_CASES_TAC >>simp[]
  >- (
    strip_tac>>
    `wf_clause (y::acc)` by fs[wf_clause_def]>>
    first_x_assum drule>>
    disch_then drule>>
    simp[]>>
    metis_tac[APPEND_ASSOC])
  >>
  ntac 2 TOP_CASE_TAC>>rw[]>>simp[]>>
  fs[wf_clause_def]
QED

Theorem parse_clause_witness_wf:
  parse_clause_witness (x::xs) = SOME (a,b,c) ⇒
  wf_clause a ∧
  case a of [] => T
  | h::t => case b of NONE => T | SOME w => MEM h w
Proof
  simp[parse_clause_witness_def]>>
  every_case_tac>>simp[]>>
  strip_tac>> drule parse_until_k_wf>>simp[wf_clause_def]>>
  rw[]>>
  metis_tac[]
QED

val parse_PR_hint_def = tDefine "parse_PR_hint" `
  parse_PR_hint id xs acc =
  if id = 0 then
    if xs = [] then SOME acc
    else NONE
  else
  case parse_until_nn xs [] of
    NONE => NONE
  | SOME (n,clause,rest) =>
      parse_PR_hint n rest ((id,clause)::acc)`
  (WF_REL_TAC `measure (LENGTH o (FST o SND))`>>
  rw[]>>
  drule parse_until_nn_length>>fs[])

(* LPR parser *)
val parse_lprstep_def = Define`
  (parse_lprstep (cid::first::rest) =
  if first = INL (strlit "d") then
    (* deletion line *)
    (case parse_until_nn rest [] of
       SOME (n, ls, []) => if n = 0 then SOME (Delete ls) else NONE
      | _ => NONE)
  else
  case cid of
    INL _ => NONE
  | INR l =>
    if l ≥ 0 then
      (* PR line *)
      case parse_clause_witness (first::rest) of
        NONE => NONE
      | SOME (clause,witness,rest) =>
        case parse_until_nn rest [] of
          NONE => NONE
        | SOME (id,hint,rest) =>
          case parse_PR_hint id rest [] of
            NONE => NONE
          | SOME sp =>
              SOME (PR (Num l) clause witness hint sp)
    else NONE
  ) ∧
  (parse_lprstep _ = NONE)`

Theorem parse_lprstep_wf:
  parse_lprstep ls = SOME lpr ⇒
  wf_lpr lpr
Proof
  Cases_on`ls`>>simp[parse_lprstep_def]>>
  Cases_on`t`>>simp[parse_lprstep_def]>>
  IF_CASES_TAC>>simp[]
  >-
    (every_case_tac>>rw[]>>simp[wf_lpr_def])
  >>
  every_case_tac>>rw[]>>simp[wf_lpr_def]>>
  drule parse_clause_witness_wf>>
  simp[]
QED

(* Mostly semantic!*)
val parse_lpr_def = Define`
  (parse_lpr [] = SOME []) ∧
  (parse_lpr (l::ls) =
    case parse_lprstep (MAP tokenize_fast (tokens blanks l)) of
      NONE => NONE
    | SOME step =>
      (case parse_lpr ls of
        NONE => NONE
      | SOME ss => SOME (step :: ss))
    )`

Theorem parse_lpr_wf:
  ∀ls lpr.
  parse_lpr ls = SOME lpr ⇒
  EVERY wf_lpr lpr
Proof
  Induct>>fs[parse_lpr_def]>>
  ntac 2 strip_tac>>
  every_case_tac>>fs[]>>
  rw[]>>simp[]>>
  drule parse_lprstep_wf>>
  simp[]
QED

(* Parsing of top-level proofs *)
val parse_proofstep_def = Define`
  (parse_proofstep (first::rest) =
  if first = INL (strlit "d") then
    (* deletion line *)
    case parse_until_zero rest [] of
      SOME (cl ,[]) => SOME (Del cl)
    | _ => NONE
  else
    case parse_until_zero (first::rest) [] of
      SOME (cl,[]) => SOME (Add cl)
    | _ => NONE) ∧
  (parse_proofstep _ = NONE)`

val parse_proof_toks_aux_def = Define`
  (parse_proof_toks_aux [] acc = SOME (REVERSE acc)) ∧
  (parse_proof_toks_aux (t::ts) acc =
  case parse_proofstep t of
    NONE => NONE
  | SOME step => parse_proof_toks_aux ts (step::acc))`

val parse_proof_toks_def = Define`
  parse_proof_toks ls = parse_proof_toks_aux ls []`

val parse_proof_def = Define`
  parse_proof strs = parse_proof_toks (MAP toks strs)`

Theorem parse_until_zero_wf_clause:
  ∀t acc c rest.
  parse_until_zero t acc = SOME (c, rest) ∧
  wf_clause acc ⇒
  wf_clause c
Proof
  Induct>>rw[parse_until_zero_def]>>
  every_case_tac>>fs[]>>rw[]
  >-
    fs[wf_clause_def]>>
  first_x_assum drule>>disch_then match_mp_tac>>
  fs[wf_clause_def]
QED

Theorem parse_proof_toks_aux_wf_proof:
  ∀ls acc pf.
  parse_proof_toks_aux ls acc = SOME pf ∧
  EVERY wf_proof acc ⇒
  EVERY wf_proof pf
Proof
  Induct>>rw[parse_proof_toks_aux_def]>>
  every_case_tac>>fs[EVERY_REVERSE]>>
  first_x_assum match_mp_tac>>
  asm_exists_tac>>simp[]>>
  Cases_on`h`>>fs[parse_proofstep_def]>>
  every_case_tac>>fs[]>>
  imp_res_tac parse_until_zero_wf_clause>>rw[]>>
  fs[wf_clause_def,wf_proof_def]
QED

Theorem parse_proof_wf_proof:
  parse_proof ls = SOME pf ⇒
  EVERY wf_proof pf
Proof
  rw[parse_proof_def,parse_proof_toks_def]>>
  match_mp_tac parse_proof_toks_aux_wf_proof>>
  asm_exists_tac>>simp[]
QED

val print_proofstep_def = Define`
  (print_proofstep (Add cl) = print_clause cl) ∧
  (print_proofstep (Del cl) = strlit"d " ^ print_clause cl)`

val print_proof_def = Define`
  print_proof pf = MAP print_proofstep pf`

Theorem toks_strcat_d:
  toks (strlit"d " ^ y) = INL (strlit"d"):: toks y
Proof
  simp[toks_def]>>
  `strlit"d " = strlit"d" ^ str(#" ")` by
    EVAL_TAC>>
  simp[]>>
  DEP_REWRITE_TAC [mlstringTheory.tokens_append]>>simp[]>>
  CONJ_TAC>-
    EVAL_TAC>>
  qexists_tac`strlit"d"`>>EVAL_TAC
QED

Theorem parse_until_zero_print_clause:
  ∀ys acc.
  wf_clause ys
  ⇒
  parse_until_zero (toks (print_clause ys)) acc = SOME (REVERSE acc ++ ys, [])
Proof
  simp[toks_def]>>
  Induct>>rw[print_clause_def]
  >-
    EVAL_TAC
  >>
  `strlit" " = str #" "` by EVAL_TAC>>
  simp[]>>
  DEP_REWRITE_TAC[mlstringTheory.tokens_append]>>simp[]>>
  CONJ_TAC >- EVAL_TAC>>
  fs[wf_clause_def]>>
  simp[tokens_blanks_toStdString]>>
  simp[tokenize_def]>>
  simp[parse_until_zero_def]
QED

Theorem parse_proofstep_print_proofstep:
  wf_proof h ⇒
  parse_proofstep (toks (print_proofstep h)) = SOME h
Proof
  Cases_on`h`>>fs[print_proofstep_def]
  >- (
    simp[toks_strcat_d,parse_proofstep_def,wf_proof_def]>>
    simp[parse_until_zero_print_clause])>>
  simp[wf_proof_def]>>
  Cases_on`toks (print_clause l)`
  >- (
    fs[toks_def]>>
    metis_tac[tokens_print_clause_nonempty])>>
  simp[parse_proofstep_def]>>
  rw[]
  >- (
    CCONTR_TAC>>
    qpat_x_assum`_ = _` mp_tac>>
    Cases_on`l`>>simp[print_clause_def]
    >-
      EVAL_TAC>>
    `strlit" " = str #" "` by EVAL_TAC>>
    simp[toks_def]>>
    DEP_REWRITE_TAC[mlstringTheory.tokens_append]>>
    simp[tokens_blanks_toStdString,tokenize_def]>>
    EVAL_TAC)>>
  qpat_x_assum`_=_` sym_sub_tac>>
  simp[parse_until_zero_print_clause]
QED

Theorem parse_proof_toks_aux_print_proofstep:
  ∀pf acc.
  EVERY wf_proof pf ⇒
  parse_proof_toks_aux (MAP toks (MAP print_proofstep pf)) acc = SOME (REVERSE acc ++ pf)
Proof
  Induct>>rw[parse_proof_toks_aux_def]>>
  simp[parse_proofstep_print_proofstep]
QED

Theorem parse_proof_print_proof:
  EVERY wf_proof pf ⇒
  parse_proof (print_proof pf) = SOME pf
Proof
  rw[parse_proof_def,print_proof_def,parse_proof_toks_def]>>
  DEP_REWRITE_TAC [parse_proof_toks_aux_print_proofstep]>>
  simp[]
QED

(* Parse a range spec of the form i-j *)
val parse_rng_def = Define`
  parse_rng ij =
  case fields (λc. c = #"-") ij of
    [i;j] =>
    (case mlint$fromNatString i of
      NONE => NONE
    | SOME i =>
    case mlint$fromNatString j of
      NONE => NONE
    | SOME j => SOME (i,j))
  | _ => NONE`

val dimacsraw = ``[
  strlit "c this is a comment";
  strlit "p cnf 5 8 ";
  strlit "    1  4 0";
  strlit "    1  5 0";
  strlit "c this is a comment";
  strlit "    2  4 0";
  strlit "    2  5 0";
  strlit "    3  4 0";
  strlit "    3  5 0";
  strlit "-1 -2 -3 0";
  strlit "c this is a comment";
  strlit "   -4 -5 0";
  ]``;

val cnf = rconc (EVAL ``THE (parse_dimacs ^(dimacsraw))``);

val back = rconc (EVAL``print_dimacs ^cnf``);

val lprraw = ``[
  strlit"8 d 0";
  strlit"9 6 1 0 1 2 8 0";
  strlit"10 6 2 0 3 4 8 0";
  strlit"11 6 3 0 5 6 8 0";
  strlit"12 -6 4 0 1 5 7 3 0";
  strlit"12 d 1 5 3 0";
  strlit"13 -6 5 0 2 6 7 4 0";
  strlit"13 d 2 6 4 0";
  strlit"14 6 0 9 10 11 7 0";
  strlit"14 d 9 10 11 7 0";
  strlit"16 0 14 12 13 8 0";
  ]``;

val lpr = rconc (EVAL ``THE (parse_lpr ^(lprraw))``);

val check = rconc (EVAL``THE (check_lpr 0 ^(lpr) (build_fml 1 ^(cnf)))``);

val _ = export_theory ();
