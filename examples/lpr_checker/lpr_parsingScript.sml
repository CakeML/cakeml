(*
   Parsing interface for DIMACS and LPR
*)
Theory lpr_parsing
Ancestors
  misc lpr mlint
Libs
  preamble

(*
  Parses a list of strings (1 per line of a file) in
  DIMACS format.
  This parser prioritizes simplicity and it is proved
  to be invertible.
*)

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

Definition fromString_unsafe_def:
  fromString_unsafe str =
    if strlen str = 0
    then 0i
    else if strsub str 0 = #"~" ∨
            strsub str 0 = #"-"
      then ~&fromChars_unsafe (strlen str - 1)
                              (substring str 1 (strlen str - 1))
      else &fromChars_unsafe (strlen str) str
End

Definition tokenize_fast_def:
  tokenize_fast (s:mlstring) =
  if strlen s = 0 then INL s
  else if strsub s 0 = #"c" ∨ strsub s 0 = #"d" then INL s
  else INR (fromString_unsafe s)
End

Definition toks_def:
  toks s = MAP tokenize (tokens blanks s)
End

Definition toks_fast_def:
  toks_fast s = MAP tokenize_fast (tokens blanks s)
End

(* DIMACS parser *)

(*
  A clause line must end with 0, cannot contain 0s elsewhere, and is within the var bound
*)
Definition parse_clause_aux_def:
  (parse_clause_aux maxvar [] (acc:cclause) = NONE) ∧
  (parse_clause_aux maxvar [c] acc = if c = INR 0i then SOME acc else NONE) ∧
  (parse_clause_aux maxvar (x::xs) acc =
    case x of
      INR l =>
      if l = 0 ∨ Num (ABS l) > maxvar then NONE
      else parse_clause_aux maxvar xs (l::acc)
    | INL (_:mlstring) => NONE
  )
End

Definition parse_clause_def:
  parse_clause maxvar xs =
  case parse_clause_aux maxvar xs [] of
    NONE => NONE
  | SOME ls => SOME (REVERSE ls)
End

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

Definition toStdString_def:
  toStdString i = int_to_string #"-" i
End

Definition print_clause_def:
  (print_clause [] = strlit "0\n") ∧
  (print_clause (x::xs) =
    toStdString x ^ strlit(" ") ^ print_clause xs)
End

Theorem tokens_unchanged:
  EVERY ($~ o P) (explode ls) ∧ ¬ NULL (explode ls) ⇒
  tokens P ls = [ls]
Proof
  rw[] >> drule TOKENS_unchanged>>
  simp[]>>
  simp[GSYM mlstringTheory.TOKENS_eq_tokens]
QED

Theorem fromString_toStdString[simp]:
   !i:int. fromString (toStdString i) = SOME i
Proof
  simp [toStdString_def]
QED

Triviality isDigit_not_blanks:
  isDigit c ==> ~ blanks c
Proof
  CCONTR_TAC \\ fs [blanks_def] \\ fs [isDigit_def]
QED

Theorem tokens_blanks_toStdString:
  tokens blanks (toStdString h) = [toStdString h]
Proof
  match_mp_tac tokens_unchanged>>
  simp [toStdString_def, int_to_string_thm, NULL_EQ] >>
  rw [EVAL ``blanks #"-"``] >>
  irule listTheory.EVERY_MONOTONIC >>
  irule_at Any ASCIInumbersTheory.EVERY_isDigit_num_to_dec_string >>
  simp [isDigit_not_blanks]
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

Definition parse_header_line_def:
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
  | _ => NONE
End

Definition print_header_line_def:
  print_header_line v len =
  strlit ("p cnf ") ^  toStdString (&v) ^ strlit(" ") ^ toStdString (&len) ^ strlit("\n")
End

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
  simp[tokens_blanks_toStdString]>>
  EVAL_TAC>>
  simp[integerTheory.INT_POS, integerTheory.INT_GE_CALCULATE]
QED

(*
  Parse a file as DIMACS
*)

(* lines which are not comments don't start with a single "c" *)
Definition nocomment_line_def:
  (nocomment_line (INL c::cs) = (c ≠ strlit "c")) ∧
  (nocomment_line _ = T)
End

(* Produces the list of clauses in order they are read *)
Definition parse_dimacs_body_def:
  (parse_dimacs_body maxvar [] acc = SOME (REVERSE acc)) ∧
  (parse_dimacs_body maxvar (s::ss) acc =
    case parse_clause maxvar s of
      NONE => NONE
    | SOME cl => parse_dimacs_body maxvar ss (cl::acc)
  )
End

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
Definition parse_dimacs_toks_def:
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
  | [] => NONE
End

(* Parse a list of strings in DIMACS format and return a ccnf *)
Definition parse_dimacs_def:
  parse_dimacs strs =
  let tokss = MAP toks strs in
  case parse_dimacs_toks tokss of
    NONE => NONE
  | SOME (nvars, nclauses, ls) => SOME ls
End

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

Definition max_lit_def:
  (max_lit k [] = k) ∧
  (max_lit k (x::xs) = if k < ABS x then max_lit (ABS x) xs else max_lit k xs)
End

Definition print_dimacs_def:
  print_dimacs fml =
  let len = LENGTH fml in
  let v = max_lit 0 (MAP (max_lit 0) fml) in
  print_header_line (Num v) len ::
  MAP print_clause fml
End

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

(* ASCII parsing *)

(* Parse everything until the next non-positive
  and returns it *)
Definition parse_until_nn_def:
  (parse_until_nn [] acc = NONE) ∧
  (parse_until_nn (x::xs) acc =
    case x of
      INL _ => NONE
    | INR l =>
    if l ≤ 0:int then
      SOME (Num (-l), REVERSE acc, xs)
    else
      parse_until_nn xs (Num l::acc)
  )
End

Theorem parse_until_nn_length[local]:
  ∀ls acc a b c.
  parse_until_nn ls acc = SOME(a,b,c) ⇒
  LENGTH c < LENGTH ls
Proof
  Induct>>fs[parse_until_nn_def]>>
  rw[]>>every_case_tac>>fs[]>>
  first_x_assum drule>>
  fs[]
QED

(* Gets the rest of the witness *)
Definition parse_until_zero_def:
  (parse_until_zero [] acc = NONE) ∧
  (parse_until_zero (x::xs) acc =
    case x of
      INL _ => NONE
    | INR l =>
    if l = 0:int then
      SOME (REVERSE acc, xs)
    else
      parse_until_zero xs (l::acc)
  )
End

Definition parse_until_k_def:
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
      parse_until_k k xs (l::acc))
End

Definition parse_clause_witness_def:
  (parse_clause_witness [] = NONE) ∧
  (parse_clause_witness (x::xs) =
    case x of
      INL _ => NONE
    | INR l =>
    if l = 0:int then
      SOME ([], NONE , xs)
    else
      parse_until_k l xs [l])
End

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

Definition parse_PR_hint_def:
  parse_PR_hint id xs acc =
  if id = 0 then
    if xs = [] then SOME acc
    else NONE
  else
  case parse_until_nn xs [] of
    NONE => NONE
  | SOME (n,clause,rest) =>
      parse_PR_hint n rest ((id,clause)::acc)
Termination
  WF_REL_TAC `measure (LENGTH o (FST o SND))`>>
  rw[]>>
  drule parse_until_nn_length>>fs[]
End

(* LPR parser *)
Definition parse_lprstep_def:
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
  (parse_lprstep _ = NONE)
End

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
Definition parse_lpr_def:
  (parse_lpr [] = SOME []) ∧
  (parse_lpr (l::ls) =
    case parse_lprstep (MAP tokenize_fast (tokens blanks l)) of
      NONE => NONE
    | SOME step =>
      (case parse_lpr ls of
        NONE => NONE
      | SOME ss => SOME (step :: ss))
    )
End

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
Definition parse_proofstep_def:
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
  (parse_proofstep _ = NONE)
End

Definition parse_proof_toks_aux_def:
  (parse_proof_toks_aux [] acc = SOME (REVERSE acc)) ∧
  (parse_proof_toks_aux (t::ts) acc =
  case parse_proofstep t of
    NONE => NONE
  | SOME step => parse_proof_toks_aux ts (step::acc))
End

Definition parse_proof_toks_def:
  parse_proof_toks ls = parse_proof_toks_aux ls []
End

Definition parse_proof_def:
  parse_proof strs = parse_proof_toks (MAP toks strs)
End

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

Definition print_proofstep_def:
  (print_proofstep (Add cl) = print_clause cl) ∧
  (print_proofstep (Del cl) = strlit"d " ^ print_clause cl)
End

Definition print_proof_def:
  print_proof pf = MAP print_proofstep pf
End

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
Definition parse_rng_def:
  parse_rng ij =
  let (i,j) = splitl (λc. c <> #"-") ij in
    (case mlint$fromNatString i of
      NONE => NONE
    | SOME i =>
    if strlen j = 0 then NONE else
    case mlint$fromNatString (substring j 1 (strlen j - 1)) of
      NONE => NONE
    | SOME j => SOME (i,j))
End

Definition print_rng_def:
  print_rng (i:num) (j:num) = toString i ^ «-» ^ toString j
End

Theorem parse_rng_print_rng:
  parse_rng (print_rng i j) = SOME (i,j)
Proof
  rw[parse_rng_def,print_rng_def]>>
  simp[mlstringTheory.splitl_SPLITL,SPLITL_def]>>
  PURE_REWRITE_TAC [GSYM STRCAT_ASSOC]>>
  PURE_REWRITE_TAC [Once SPLITP_APPEND]>>
  IF_CASES_TAC
  >- (
    CCONTR_TAC>>pop_assum kall_tac>>
    pop_assum mp_tac>>simp[o_DEF,mlintTheory.num_to_str_thm]>>
    `EVERY isDigit (toString i)` by
      metis_tac[ASCIInumbersTheory.EVERY_isDigit_num_to_dec_string]>>
    pop_assum mp_tac>>match_mp_tac MONO_EVERY>>
    EVAL_TAC>>rw[])>>
  simp[SPLITP,mlstringTheory.implode_def,mlstringTheory.substring_def]>>
  simp[GSYM mlstringTheory.implode_def]>>
  `1:num = SUC 0` by simp[]>>
  pop_assum SUBST_ALL_TAC>>
  simp[Once SEG_SUC_CONS]>>
  `strlen (toString j) = LENGTH (explode (toString j))` by
    simp[]>>
  pop_assum SUBST1_TAC>>simp[SEG_LENGTH_ID]
QED

(*
  Parse a string as variable byte encoded numbers
  Terminated with 0 (last character skipped in parsing)
*)
Definition parse_vb_string_aux_def:
  parse_vb_string_aux (str:mlstring) (i:num) (len:num) (ex:num) (n:num) (acc:num list) =
  if i < len then
    let v = ORD (strsub str i) in
      if v >= 128 then (* msb is set *)
        parse_vb_string_aux str (i+1) len (ex*128) ((v-128)*ex+n) acc
      else
        parse_vb_string_aux str (i+1) len 1 0 (v*ex+n::acc)
  else
    acc
Termination
  WF_REL_TAC` measure (λ(x,s,i,r). i-s)`
End

Definition parse_vb_string_def:
  parse_vb_string x =
  parse_vb_string_aux x 0 (strlen x - 1) 1 0 []
End

(* Parses either:
  INR
  'a' (variable-byte encoded list of numbers ) 0 ...
or
  INL (Del ...)
  'd' (variable-byte encoded list of numbers ) 0
*)
Definition parse_vb_string_head_def:
  parse_vb_string_head x =
  if strlen x = 0 then NONE
  else
  let c = strsub x 0 in
  let ls = parse_vb_string_aux x 1 (strlen x - 1) 1 0 [] in
  if c = #"a"
  then
    SOME (INR ls)
  else if c = #"d"
  then
    SOME (INL (Delete (MAP (λn. n DIV 2) ls)))
  else NONE
End

(* Turn numbers back into ints *)
Definition clausify_aux_def:
  (clausify_aux [] acc = acc) ∧
  (clausify_aux (x::xs) acc =
  if x < 2n then clausify_aux xs acc
  else
    let v =
      (if x MOD 2 = 0n
      then (&(x DIV 2):int)
      else (-&(x DIV 2):int)) in
      clausify_aux xs (v::acc))
End

Definition clausify_def:
  clausify cls = clausify_aux cls []
End

(* Split list of numbers at k *)
Definition parse_vb_until_k_def:
  (parse_vb_until_k k [] acc = (acc, NONE)) ∧
  (parse_vb_until_k k (l::xs) acc =
    if l = k then
      (acc, SOME (k::xs))
    else
      parse_vb_until_k k xs (l::acc))
End

Definition parse_vb_clause_witness_def:
  (parse_vb_clause_witness [] = ([],NONE)) ∧
  (parse_vb_clause_witness (l::xs) =
      parse_vb_until_k l xs [l])
End

(* Parse everything until the next negative and returns it *)
Definition parse_vb_until_nn_def:
  (parse_vb_until_nn [] acc = (0, REVERSE acc, [])) ∧
  (parse_vb_until_nn (l::xs) acc =
    if l <= 0:int then
      (Num (-l), REVERSE acc, xs)
    else
      parse_vb_until_nn xs (Num l::acc)
  )
End

Triviality parse_vb_until_nn_length:
  ∀ls acc a b c.
  parse_vb_until_nn ls acc = (a,b,c) ∧ a ≠ 0 ⇒
  LENGTH c < LENGTH ls
Proof
  Induct>>fs[parse_vb_until_nn_def]>>
  rw[]>>every_case_tac>>fs[]>>
  first_x_assum drule>>
  fs[]
QED

Definition parse_vb_PR_hint_def:
  parse_vb_PR_hint id xs acc =
  if id = 0 then acc
  else
  case parse_vb_until_nn xs [] of (n,clause,rest) =>
    if n = 0 then ((id,clause)::acc)
    else parse_vb_PR_hint n rest ((id,clause)::acc)
Termination
  (WF_REL_TAC `measure (LENGTH o (FST o SND))`>>
  rw[]>>
  drule parse_vb_until_nn_length>>fs[])
End

(* All parsing steps related to PR *)
Definition do_PR_def:
  do_PR ls ys =
  let rs = parse_vb_string ys in
  let (lss:int list) = clausify ls in
  let (rss:int list) = clausify rs in
  case lss of [] => NONE
  | (x::xs) =>
    if x ≥ 0 then
      case parse_vb_clause_witness xs of (clause,witness) =>
      let clause = REVERSE clause in
      case parse_vb_until_nn rss [] of (id,hint,rss) =>
      case parse_vb_PR_hint id rss [] of sp =>
      SOME (PR (Num x) clause witness hint sp)
    else NONE
End

Theorem clausify_aux_non_zero:
  ∀ls acc acc'.
  ¬MEM 0 acc ∧
  clausify_aux ls acc = acc' ⇒
  ¬MEM 0 acc'
Proof
  Induct>>rw[clausify_aux_def]>>gvs[]>>
  first_x_assum match_mp_tac>>
  simp[]>>
  intLib.ARITH_TAC
QED

Theorem parse_vb_until_k_wf:
  ∀xs acc clause witness.
  ¬MEM (0:int) acc ∧
  ¬MEM 0 xs ∧
  parse_vb_until_k h xs acc = (clause,witness) ⇒
  ∃front.
  clause = front ++ acc ∧
  ¬MEM 0 clause ∧
  case witness of NONE => T | SOME w => MEM h w
Proof
  Induct>>rw[parse_vb_until_k_def]>>gvs[]>>
  first_x_assum (drule_at (Pos last))>>
  simp[]>>rw[]>>
  simp[]
QED

Theorem parse_vb_clause_witness_wf:
  ¬MEM (0:int) xs ∧
  parse_vb_clause_witness xs = (clause,witness) ⇒
  ¬MEM (0:int) clause ∧
  case REVERSE clause of
    [] => T
  | h::t => (case witness of NONE => T | SOME w => MEM h w)
Proof
  Cases_on`xs`>>rw[parse_vb_clause_witness_def]>>
  drule_at (Pos last) parse_vb_until_k_wf>>
  simp[]>>rw[]>>
  every_case_tac>>gvs[]
QED

Theorem do_PR_wf_lpr:
  do_PR ls ys = SOME res ⇒
  wf_lpr res
Proof
  rw[do_PR_def,AllCaseEqs()]>>
  fs[wf_lpr_def]>>
  gvs[clausify_def]>>
  drule_at Any clausify_aux_non_zero>>strip_tac>>gvs[]>>
  drule_all parse_vb_clause_witness_wf>>
  simp[wf_clause_def]
QED

(* For testing *)
Definition parse_pr_def:
  parse_pr ls =
  case ls of [] => []
  | x::xs =>
  case parse_vb_string_head x of
    NONE => []
  | SOME (INL d) => d::parse_pr xs
  | SOME (INR r) =>
    (case xs of [] => []
    | y::ys =>
      (case do_PR r y of NONE => []
      | SOME p => p :: parse_pr ys))
End

(* Guessing whether we're in binary based on the first character

  In ASCII: the first character is always a number
  In binary: the first character is always #"a" or #"d"
*)

Definition good_char_def:
  good_char c ⇔
  c = #"a" ∨ c = #"d"
End

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

val res = EVAL ``good_char (strsub (HD ^(lprraw)) 0)``

val clprraw = `` [
 (implode o (MAP CHR)) [97;92;37;39;41;0];
 (implode o (MAP CHR)) [60;48;80;68;28;40;82;88; 6; 0];
 (implode o (MAP CHR)) [97;94;27;39;41; 0];
 (implode o (MAP CHR)) [58;48;78;68; 6;16;82;86;24; 0];
 (implode o (MAP CHR)) [97;96;39;41; 0];
 (implode o (MAP CHR)) [80;78;68;48;58;60;94;88;26;36;82;86; 4; 0];
 (implode o (MAP CHR)) [100;94;92; 0];
 (implode o (MAP CHR)) [97;98; 3;29;41; 0;36;32;78;74; 2; 4;84;86;50; 0];
]``

val res = EVAL ``good_char (strsub (HD ^(clprraw)) 0)``

val res = EVAL``parse_pr ^(clprraw)``

