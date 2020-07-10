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

(* TODO: mlint fromString should return NONE on empty *)
val tokenize_def = Define`
  tokenize (s:mlstring) =
  case mlint$fromString s of
    NONE => INL s
  | SOME i => INR i`

val toks_def = Define`
  toks s = MAP tokenize (tokens blanks s)`

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
  parse strings as DIMACS
  For the DIMACS file, the *entire* file is read at once
*)
val build_fml_def = Define`
  (build_fml maxvar (id:num) [] (acc:ccnf) = SOME acc) ∧
  (build_fml maxvar id (s::ss) acc =
    case parse_clause maxvar s of
    NONE => NONE
  | SOME cl => build_fml maxvar (id+1) ss (insert id cl acc))`

(* lines which are not comments don't start with a single "c" *)
val nocomment_line_def = Define`
  (nocomment_line (INL c::cs) = (c ≠ strlit "c")) ∧
  (nocomment_line _ = T)`

val parse_dimacs_toks_def = Define`
  parse_dimacs_toks tokss =
  let nocomments = FILTER nocomment_line tokss in
  case nocomments of
    s::ss =>
      (case parse_header_line s of
      SOME (vars,clauses) =>
         if LENGTH ss = clauses then
          case build_fml vars 1 ss LN of NONE => NONE
          | SOME acc => SOME (vars,acc)
        else NONE
      | NONE => NONE)
  | [] => NONE`

val parse_dimacs_def = Define`
  parse_dimacs strs =
  let tokss = MAP toks strs in
  parse_dimacs_toks tokss`

Theorem build_fml_wf_fml:
  ∀ls mv id acc acc'.
  wf_fml acc ∧ build_fml mv id ls acc = SOME acc' ⇒
  wf_fml acc'
Proof
  Induct>>rw[build_fml_def]>>fs[]>>
  every_case_tac>>fs[]>>
  imp_res_tac parse_clause_wf_clause>>fs[]>>
  metis_tac[wf_fml_insert,parse_clause_wf_clause,wf_clause_def,MEM_REVERSE]
QED

Theorem build_fml_bound:
  ∀ls mv id acc acc'.
  build_fml mv id ls acc = SOME acc' ∧
  (∀C. C ∈ values acc ⇒ EVERY (λi. Num (ABS i) <= mv) C) ⇒
  (∀C. C ∈ values acc' ⇒ EVERY (λi. Num (ABS i) <= mv) C)
Proof
  Induct>>rw[build_fml_def]>>fs[]>>
  every_case_tac>>fs[]>>
  imp_res_tac parse_clause_bound>>fs[]>>
  first_x_assum drule>>
  disch_then match_mp_tac>>fs[]>>
  rw[]>>drule values_insert>>rw[]>>
  metis_tac[]
QED

Theorem parse_dimacs_wf_bound:
  parse_dimacs strs = SOME (maxvars, fml) ⇒
  wf_fml fml ∧
  (∀C. C ∈ values fml ⇒ EVERY (λi. Num (ABS i) <= maxvars) C)
Proof
  simp[parse_dimacs_def,parse_dimacs_toks_def]>>
  every_case_tac>>fs[]>>
  strip_tac>>
  CONJ_TAC>>
  TRY(match_mp_tac build_fml_wf_fml)>>
  TRY(match_mp_tac build_fml_bound)>>
  qmatch_asmsub_abbrev_tac`build_fml a b c d`>>
  qexists_tac`c`
  >- (
    qexists_tac`a`>>
    qexists_tac`b`>>
    qexists_tac`d`>>
    unabbrev_all_tac>>fs[wf_fml_def,values_def,lookup_def])
  >>
    qexists_tac`b`>>
    qexists_tac`d`>>
    unabbrev_all_tac>>fs[wf_fml_def,values_def,lookup_def]
QED

val max_lit_def = Define`
  (max_lit k [] = k) ∧
  (max_lit k (x::xs) = if k < ABS x then max_lit (ABS x) xs else max_lit k xs)`

(* print a formula out to DIMACS *)
val print_dimacs_def = Define`
  print_dimacs fml =
  let ls = MAP SND (toSortedAList fml) in
  let len = LENGTH ls in
  let v = max_lit 0 (MAP (max_lit 0) ls) in
  print_header_line (Num v) len ::
  MAP print_clause ls`

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

Theorem build_fml_MAP_print_clause:
  ∀vs id acc.
  EVERY (λc. EVERY (λl. Num (ABS l) ≤ mv) c) vs ∧
  EVERY wf_clause vs ∧
  (∀x. x ∈ domain acc ⇒ x < id)
  ⇒
  ∃acc'.
  build_fml mv id (MAP toks (MAP print_clause vs)) acc = SOME acc' ∧
  values acc' = values acc ∪ set vs
Proof
  Induct>>rw[build_fml_def]>>
  drule parse_clause_print_clause>> rw[]>>
  fs[]>>
  first_x_assum(qspecl_then[`id+1`,`insert id h acc`] mp_tac)>>
  impl_tac>- (
    rw[domain_insert]>>
    fs[]>>
    first_x_assum drule>>fs[])>>
  rw[]>>
  simp[]>>
  simp[values_def,lookup_insert,EXTENSION]>>
  rw[EQ_IMP_THM]>>pop_assum mp_tac>>rw[]
  >- metis_tac[]
  >- (
    `n ∈ domain acc` by metis_tac[domain_lookup]>>
    first_x_assum drule>>fs[]>>
    strip_tac>>DISJ1_TAC>>qexists_tac`n`>>
    fs[])
  >- metis_tac[]
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

Theorem parse_dimacs_print_dimacs:
  wf_fml fml ⇒
  ∃mv fml'.
  parse_dimacs (print_dimacs fml) = SOME (mv, fml') ∧
  values fml = values fml'
Proof
  simp[parse_dimacs_def,print_dimacs_def,parse_dimacs_toks_def]>>
  qmatch_goalsub_abbrev_tac`print_header_line a b`>>
  simp[Once toks_def]>>
  assume_tac print_header_line_first>>fs[]>>
  pop_assum sym_sub_tac>>
  `tokenize (strlit "p") = INL (strlit "p")` by
    EVAL_TAC>>
  simp[nocomment_line_def]>>
  simp[parse_header_line_print_header_line]>>
  unabbrev_all_tac>>
  simp[FILTER_print_clause]>>
  qmatch_goalsub_abbrev_tac`build_fml mv id (_ _ ( _ _ vs))`>>
  strip_tac>>
  qspecl_then [`vs`,`id`,`LN`] mp_tac build_fml_MAP_print_clause>>
  impl_tac >- (
    simp[]>>
    CONJ_TAC >-
      fs[Abbr`mv`,max_lit_max_lit_max]>>
    fs[Abbr`vs`,EVERY_MAP,EVERY_MEM,wf_fml_def,values_def,FORALL_PROD,MEM_toSortedAList]>>
    metis_tac[])>>
  rw[]>>
  simp[]>>
  fs[lookup_def,values_def,Abbr`vs`,EXTENSION,MEM_MAP,EXISTS_PROD,MEM_toSortedAList]
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
      parse_PR_hint n rest (insert id clause acc)`
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
          case parse_PR_hint id rest LN of
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
    case parse_lprstep (toks l) of
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

val back = rconc (EVAL``print_dimacs (SND ^cnf)``);

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

val check = rconc (EVAL``THE (check_lpr ^(lpr) (SND ^(cnf)))``);

val _ = export_theory ();
