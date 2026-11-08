(*
  Parse and print for pbc, npbc_check
*)
Theory pb_parse
Ancestors
  pbc pbc_normalise name_table npbc_check mlint
Libs
  preamble

val _ = numLib.temp_prefer_num();

(*
  Printing for pseudo-Boolean problems in (extended) OPB format
*)

(* Printing mlstring pbc *)
Definition lit_string_def:
  (lit_string (Pos v) = v) ∧
  (lit_string (Neg v) = «~» ^ v)
End

Definition lhs_string_def:
  lhs_string xs =
  concatWith « » (MAP(λ(c,l). concat [int_to_string #"-" c; « » ; lit_string l]) xs)
End

Definition op_string_def:
  (op_string GreaterEqual = « >= ») ∧
  (op_string Greater = « > ») ∧
  (op_string LessEqual = « <= ») ∧
  (op_string Less = « < »)
End

Definition rel_string_def:
  (rel_string REq = « = ») ∧
  (rel_string (RIneq op) = op_string op)
End

Definition lits_string_def:
  lits_string ls = concatWith « » (MAP lit_string ls)
End

(* An unreified constraint prints exactly as before, with no arrow *)
Definition pbc_string_def:
  (pbc_string (Fwd [] rel,xs,i) =
    concat [
      lhs_string xs;
      rel_string rel;
      int_to_string #"-" i; « ;\n»]) ∧
  (pbc_string (Fwd ls rel,xs,i) =
    concat [
      lits_string ls; « ==> »;
      lhs_string xs;
      rel_string rel;
      int_to_string #"-" i; « ;\n»]) ∧
  (pbc_string (Bwd l op,xs,i) =
    concat [
      lit_string l; « <== »;
      lhs_string xs;
      op_string op;
      int_to_string #"-" i; « ;\n»]) ∧
  (pbc_string (Iff l op,xs,i) =
    concat [
      lit_string l; « <==> »;
      lhs_string xs;
      op_string op;
      int_to_string #"-" i; « ;\n»])
End

Definition annot_pbc_string_def:
  annot_pbc_string (annots,str) =
    concat (MAP (λl. concat [«@»;l; « »]) annots ++ [pbc_string str])
End

(* printing a string pbf, possibly with string annotation *)
Definition obj_string_def:
  obj_string (f,c:int) =
  let c_string =
    if c = 0 then «» else
    « » ^
      int_to_string #"-" c in
  «min: » ^ lhs_string f ^ c_string ^ « ;\n»
End

Definition pres_string_def:
  pres_string pres =
  let c_string =
    concatWith « » pres in
  «preserved: » ^ c_string ^ « ;\n»
End

(* Problem without annotation *)
Definition print_prob_def:
  print_prob (pres,obj,fml) =
  let obstr = case obj of NONE => [] | SOME fc => [obj_string fc] in
  let presstr = case pres of NONE => [] | SOME p => [pres_string p] in
    obstr ++ presstr ++ MAP pbc_string fml
End

(* Problem with annotation *)
Definition print_annot_prob_def:
  print_annot_prob (pres,obj,fml) =
  let obstr = case obj of NONE => [] | SOME fc => [obj_string fc] in
  let presstr = case pres of NONE => [] | SOME p => [pres_string p] in
    obstr ++ presstr ++ MAP annot_pbc_string fml
End

(* Strips annotations *)
Definition strip_annot_prob_def:
  strip_annot_prob (pres,obj,afml) =
  (pres,obj,MAP SND afml)
End

(***
  Printing normalised constraints.

  Variables are numbered rather than named, so a coefficient carries the sign
  of its literal: (c,v) prints as |c| x_v when c is positive and |c| ~x_v when
  it is negative.

  As for pbc, the fragments carry no line terminator and npbc_string prints one
  constraint per line.
***)

Definition coeff_lit_string_def:
  coeff_lit_string (c,v:var) =
    if c < 0
    then toString (Num ~c) ^ « ~x»^ toString v
    else toString (Num c) ^ « x»^ toString v
End

Definition npbc_lhs_string_def:
  npbc_lhs_string (xs: ((int # var) list)) =
  concatWith « »
    (MAP coeff_lit_string xs)
End

Definition npbc_constr_string_def:
  (npbc_constr_string (xs,i:int) =
    concat [
      npbc_lhs_string xs;
      « >= »;
      int_to_string #"-" i; «;»])
End

Definition npbc_string_def:
  npbc_string c = npbc_constr_string c ^ «\n»
End

(*
  Parse an OPB file as a string-variabled PB problem
*)

(* TODO: copied from lpr_parsing *)
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

(* One pass over a line computing toks (toks_scan_toks below).
  The token being read spans s[i..j); m is the scanner state:
  0 between tokens, 1 after a leading sign (~, - or +), 2 in a run of digits
  (acc holds their value, neg the sign, k counts them up to 9),
  3 in a token that is not a number.
  Arithmetic is on small integers (mlint's smallnum functions): indices with s as the
  witness, character codes below 256, and the first nine digits of a number,
  whose value stays below 10 ** 9 < 2 ** 30; later digits use unbounded
  arithmetic. *)
Definition scan_tok_def:
  scan_tok s (m:num) neg (acc:num) i j =
  if smallnum_eq m 2 then INR (if neg then -&acc else &acc:int)
  else INL (substring s i (smallnum_sub_str j i s))
End

(* TMC *)
Definition scan_toks_def:
  scan_toks s n (m:num) neg (acc:num) (k:num) i j =
  if smallnum_lt_str j n s then
    let oc = ORD (strsub_unsafe s j) in
    let j1 = smallnum_add_str j 1 s in
    if ¬smallnum_lt 32 oc ∧
       (smallnum_eq oc 32 ∨ smallnum_eq oc 10 ∨ smallnum_eq oc 9 ∨ smallnum_eq oc 13)
    then
      if smallnum_eq m 0 then scan_toks s n 0 F 0 0 j1 j1
      else
        let t = scan_tok s m neg acc i j in
        t :: scan_toks s n 0 F 0 0 j1 j1
    else if smallnum_eq m 3 then scan_toks s n 3 F 0 0 i j1
    else if smallnum_eq m 0 then
      if smallnum_le 48 oc ∧ smallnum_le oc 57 then
        scan_toks s n 2 F (smallnum_sub oc 48) 1 j j1
      else if smallnum_eq oc 126 ∨ smallnum_eq oc 45 then
        scan_toks s n 1 T 0 0 j j1
      else if smallnum_eq oc 43 then scan_toks s n 1 F 0 0 j j1
      else scan_toks s n 3 F 0 0 j j1
    else if smallnum_le 48 oc ∧ smallnum_le oc 57 then
      if smallnum_lt k 9 then
        scan_toks s n 2 neg
          (smallnum_add (smallnum_mul acc 10) (smallnum_sub oc 48))
          (smallnum_add k 1) i j1
      else scan_toks s n 2 neg (acc * 10 + smallnum_sub oc 48) k i j1
    else scan_toks s n 3 F 0 0 i j1
  else if smallnum_eq m 0 then []
  else [scan_tok s m neg acc i j]
Termination
  WF_REL_TAC`measure (λ(s,n,m,neg,acc,k,i,j). n - j)`>>
  rw[smallnum_lt_str_def,smallnum_add_str_def]
End

(* What scan_toks knows about the token s[i..j) it is reading in state m *)
Definition scan_inv_def:
  scan_inv s m neg acc k i j ⇔
    m ≤ (3:num) ∧
    (m = 0 ⇒ i = j) ∧
    (m ≠ 0 ⇒ i < j ∧ ∀q. i ≤ q ∧ q < j ⇒ ¬blanks (strsub s q)) ∧
    (m = 1 ⇒ j = i + 1 ∧ acc = 0 ∧ k = 0 ∧
      (strsub s i = #"~" ∨ strsub s i = #"-" ∨ strsub s i = #"+") ∧
      (neg ⇔ strsub s i = #"~" ∨ strsub s i = #"-")) ∧
    (m = 2 ⇒ ∃p.
      (p = i ∧ ¬neg ∨
       p = i + 1 ∧ (strsub s i = #"~" ∨ strsub s i = #"-" ∨ strsub s i = #"+") ∧
       (neg ⇔ strsub s i = #"~" ∨ strsub s i = #"-")) ∧
      p < j ∧ (∀q. p ≤ q ∧ q < j ⇒ isDigit (strsub s q)) ∧
      acc = fromChars_range_unsafe p (j - p) s ∧ k = MIN (j - p) 9) ∧
    (m = 3 ⇒ ∃q. i ≤ q ∧ q < j ∧ ¬isDigit (strsub s q) ∧
      (q = i ⇒ strsub s i ≠ #"~" ∧ strsub s i ≠ #"-" ∧ strsub s i ≠ #"+"))
End

Theorem scan_tok_tokenize[local]:
  scan_inv s m neg acc k i j ∧ m ≠ 0 ∧ j ≤ strlen s ⇒
  scan_tok s m neg acc i j = tokenize (substring s i (j - i))
Proof
  simp[scan_tok_def,smallnum_eq_def,smallnum_sub_str_def,tokenize_def]>>
  strip_tac>>
  IF_CASES_TAC
  >- (
    gvs[scan_inv_def]
    >- (
      `isDigit (strsub s i)` by simp[]>>
      `strsub s i ≠ #"~" ∧ strsub s i ≠ #"-" ∧ strsub s i ≠ #"+"` by
        (rpt strip_tac>>fs[]>>qpat_x_assum `isDigit _` mp_tac>>EVAL_TAC)>>
      rw[mlintTheory.fromString_def,mlstringTheory.strlen_substring,
         strsub_substring]>>
      DEP_REWRITE_TAC [fromChars_substring_SOME]>>
      simp[])>>
    rw[mlintTheory.fromString_def,mlstringTheory.strlen_substring,
       strsub_substring,substring_substring]>>
    DEP_REWRITE_TAC [fromChars_substring_SOME]>>
    simp[])>>
  `fromString (substring s i (j − i)) = NONE` suffices_by simp[]>>
  Cases_on`m = 1`
  >- (
    gvs[scan_inv_def]>>
    simp[mlintTheory.fromString_def,mlstringTheory.strlen_substring,
         strsub_substring,mlintTheory.fromChars_def])>>
  gvs[scan_inv_def]>>
  `m = 3` by decide_tac>>
  gvs[]>>
  rw[mlintTheory.fromString_def,mlstringTheory.strlen_substring,strsub_substring,
     substring_substring]>>
  irule fromChars_substring_NONE>>
  simp[]>>
  qexists_tac`q`>>
  gvs[]
QED

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

Theorem one_point_range[local]:
  ((∀q. i ≤ q ∧ q < i + 1 ⇒ P q) ⇔ P i) ∧
  ((∃q. i ≤ q ∧ q < i + 1 ∧ Q q) ⇔ Q (i:num))
Proof
  rw[EQ_IMP_THM]
  >- (`q = i` by decide_tac>>gvs[])
  >- (`q = i` by decide_tac>>gvs[])>>
  qexists_tac`i`>>simp[]
QED

(* TODO: move to mlintTheory *)
Theorem fromChars_range_unsafe_1[local]:
  fromChars_range_unsafe l 1 s = ORD (strsub s l) − 48
Proof
  REWRITE_TAC[ONE,mlintTheory.fromChars_range_unsafe_def,
              mlintTheory.fromChar_unsafe_def]>>
  simp[]
QED

Theorem range_snoc[local]:
  i ≤ j ⇒
  ((∀q. i ≤ q ∧ q < j + 1 ⇒ P q) ⇔ (∀q. i ≤ q ∧ q < j ⇒ P q) ∧ P (j:num))
Proof
  rw[EQ_IMP_THM]>>
  Cases_on`q = j`>>gvs[]
QED

Theorem scan_inv_2_intro[local]:
  (p = i ∧ ¬neg ∨
   p = i + 1 ∧ (strsub s i = #"~" ∨ strsub s i = #"-" ∨ strsub s i = #"+") ∧
   (neg ⇔ strsub s i = #"~" ∨ strsub s i = #"-")) ∧
  i < j ∧ (∀q. i ≤ q ∧ q < j ⇒ ¬blanks (strsub s q)) ∧
  p < j ∧ (∀q. p ≤ q ∧ q < j ⇒ isDigit (strsub s q)) ∧
  acc = fromChars_range_unsafe p (j - p) s ∧ k = MIN (j - p) 9 ⇒
  scan_inv s 2 neg acc k i j
Proof
  rw[scan_inv_def]
  >- (qexists_tac`i`>>simp[])>>
  qexists_tac`i + 1`>>simp[]
QED

Theorem scan_inv_digit[local]:
  scan_inv s m neg acc k i j ∧ m ≠ 0 ∧ m ≠ 3 ∧ j < strlen s ∧
  ¬blanks (strsub s j) ∧ 48 ≤ ORD (strsub s j) ∧ ORD (strsub s j) ≤ 57 ⇒
  scan_inv s 2 neg (10 * acc + ORD (strsub s j) − 48)
    (if k < 9 then k + 1 else k) i (j + 1)
Proof
  strip_tac>>
  `i < j ∧ ∀q. i ≤ q ∧ q < j ⇒ ¬blanks (strsub s q)` by fs[scan_inv_def]>>
  `∃p. (p = i ∧ ¬neg ∨
        p = i + 1 ∧ (strsub s i = #"~" ∨ strsub s i = #"-" ∨ strsub s i = #"+") ∧
        (neg ⇔ strsub s i = #"~" ∨ strsub s i = #"-")) ∧
       p ≤ j ∧ (∀q. p ≤ q ∧ q < j ⇒ isDigit (strsub s q)) ∧
       acc = fromChars_range_unsafe p (j - p) s ∧ k = MIN (j - p) 9` by (
    Cases_on`m = 1`
    >- (
      `j = i + 1 ∧ acc = 0 ∧ k = 0 ∧
       (strsub s i = #"~" ∨ strsub s i = #"-" ∨ strsub s i = #"+") ∧
       (neg ⇔ strsub s i = #"~" ∨ strsub s i = #"-")` by fs[scan_inv_def]>>
      qexists_tac`j`>>
      simp[mlintTheory.fromChars_range_unsafe_def])>>
    `m = 2` by fs[scan_inv_def]>>
    fs[scan_inv_def]>>
    qexists_tac`p`>>
    simp[])>>
  irule scan_inv_2_intro>>
  (
    conj_tac >- simp[range_snoc]>>
    conj_tac >- simp[]>>
    qexists_tac`p`>>
    simp[range_snoc,fromChars_range_unsafe_snoc,isDigit_def]>>
    rw[MIN_DEF])
QED

Theorem scan_toks_tokens_alt_aux[local]:
  ∀s n m neg acc k i j.
  n = strlen s ∧ j ≤ n ∧ scan_inv s m neg acc k i j ⇒
  scan_toks s n m neg acc k i j = MAP tokenize (tokens_alt_aux blanks s i j n)
Proof
  ho_match_mp_tac scan_toks_ind>>
  rpt gen_tac>>
  strip_tac>>
  rpt strip_tac>>
  simp[Once scan_toks_def,Once mlstringTheory.tokens_alt_aux_def]>>
  fs[smallnum_lt_str_def,smallnum_add_str_def,smallnum_eq_def,smallnum_lt_def,
     smallnum_le_def,smallnum_sub_def,smallnum_add_def,smallnum_mul_def,
     mlstringTheory.strsub_unsafe_eq_strsub,scan_blank,scan_nonblank]>>
  reverse (Cases_on`j < strlen s`)
  >- (
    `j = strlen s` by decide_tac>>
    Cases_on`m = 0`
    >- gvs[scan_inv_def]>>
    `i ≠ j` by fs[scan_inv_def]>>
    simp[]>>
    irule scan_tok_tokenize>>
    simp[]>>
    qexists_tac`k`>>
    gvs[])>>
  Cases_on`blanks (strsub s j)`
  >- (
    Cases_on`m = 0`
    >- (
      `i = j` by fs[scan_inv_def]>>
      gvs[]>>
      qpat_x_assum `scan_inv s 0 F 0 0 _ _ ⇒ _` irule>>
      simp[scan_inv_def])>>
    `i ≠ j` by fs[scan_inv_def]>>
    gvs[]>>
    conj_tac
    >- (
      irule scan_tok_tokenize>>
      simp[]>>
      qexists_tac`k`>>
      simp[])>>
    qpat_x_assum `scan_inv s 0 F 0 0 _ _ ⇒ _` irule>>
    simp[scan_inv_def])>>
  fs[]>>
  Cases_on`m = 3`
  >- (
    gvs[]>>
    qpat_x_assum `scan_inv s 3 F 0 0 i (j + 1) ⇒ _` irule>>
    gvs[scan_inv_def]>>
    rw[]
    >- (Cases_on`q' = j`>>gvs[])>>
    qexists_tac`q`>>
    simp[])>>
  Cases_on`m = 0`
  >- (
    `i = j` by fs[scan_inv_def]>>
    gvs[]>>
    rw[]>>
    first_x_assum irule>>
    simp[scan_inv_def,isDigit_def,GSYM ORD_eq_CHR,one_point_range,
         fromChars_range_unsafe_1])>>
  qpat_x_assum `m = 3 ⇒ _` kall_tac>>
  simp[]>>
  rw[]>>
  first_x_assum irule>>
  simp[]
  >- (drule_all scan_inv_digit>>simp[])
  >- (drule_all scan_inv_digit>>simp[])>>
  `i < j ∧ ∀q. i ≤ q ∧ q < j ⇒ ¬blanks (strsub s q)` by fs[scan_inv_def]>>
  simp[scan_inv_def,range_snoc]>>
  qexists_tac`j`>>
  simp[isDigit_def]
QED

Theorem toks_scan_toks:
  toks s = scan_toks s (strlen s) 0 F 0 0 0 0
Proof
  rw[toks_def,mlstringTheory.tokens_alt]>>
  irule (GSYM scan_toks_tokens_alt_aux)>>
  simp[scan_inv_def]
QED

(* OPB parser
  Parses a literal s, ~s
  Valid names may contain a-z,A-Z,0-9,[]{}_^- characters
*)
Definition parse_lit_def:
  parse_lit s =
  if strlen s ≥ 2 ∧ strsub_unsafe s 0 = #"~" then
    let ss = substring s 1 (strlen s - 1) in
    if goodString ss then
        SOME (Neg ss)
    else NONE
  else if strlen s ≥ 1 then
    if goodString s then SOME (Pos s)
    else NONE
  else NONE
End

(*
  EVAL ``parse_lit «xaAa_-1»``
  EVAL ``parse_lit «~x1234»``
  EVAL ``parse_lit «fancy_{1}^[-42]»``
*)

(* Parse the LHS of a constraint and returns the remainder of the line *)
Definition parse_constraint_LHS_aux_def:
  (parse_constraint_LHS_aux (INR n::INL v::rest) acc =
    case parse_lit v of
      NONE => (INR n::INL v::rest,REVERSE acc)
    | SOME l => parse_constraint_LHS_aux rest ((n,l)::acc)) ∧
  (parse_constraint_LHS_aux ls acc = (ls,REVERSE acc))
End

Definition parse_constraint_LHS_def:
  parse_constraint_LHS ss = parse_constraint_LHS_aux ss []
End

(* Strip ; terminator from the end of a string *)
Definition strip_term_def:
  strip_term s =
  if strlen s ≥ 1 ∧ strsub_unsafe s (strlen s - 1) = #";"
  then SOME (substring s 0 (strlen s - 1))
  else NONE
End

(* Strip ; from the end of a tokenized line and retokenize *)
Definition strip_term_line_aux_def:
  (strip_term_line_aux [] acc = NONE) ∧
  (strip_term_line_aux [x] acc =
    case x of INR n => NONE
    | INL s =>
    if s = «;»
    then SOME (REVERSE acc)
    else
        case strip_term s of
          SOME s =>
            SOME (REVERSE (tokenize s::acc))
        | NONE => NONE) ∧
  (strip_term_line_aux (x::xs) acc =
    strip_term_line_aux xs (x::acc))
End

Definition strip_term_line_def:
  strip_term_line ss = strip_term_line_aux ss []
End

(* What becomes of the last token when ; is stripped:
  NONE: the line is not terminated;
  SOME NONE: the last token is ; itself and is dropped;
  SOME (SOME t): the last token ended in ; and is replaced by t *)
Definition term_last_def:
  (term_last [] = NONE) ∧
  (term_last [x] =
    case x of INR n => NONE
    | INL s =>
    if s = «;» then SOME NONE
    else
      case strip_term s of
        SOME s => SOME (SOME (tokenize s))
      | NONE => NONE) ∧
  (term_last (x::xs) = term_last xs)
End

(* TMC *)
Definition replace_last_def:
  replace_last x xs t =
  case xs of
    [] => (case t of NONE => [] | SOME y => [y])
  | (y::ys) => x :: replace_last y ys t
End

Theorem strip_term_line_aux_last:
  ∀xs x acc.
  strip_term_line_aux (x::xs) acc =
  case term_last (x::xs) of
    NONE => NONE
  | SOME t => SOME (REVERSE acc ++ replace_last x xs t)
Proof
  Induct
  >- (
    Cases>>
    rw[strip_term_line_aux_def,term_last_def,Once replace_last_def]>>
    TOP_CASE_TAC>>
    simp[Once replace_last_def])>>
  rw[strip_term_line_aux_def,term_last_def]>>
  TOP_CASE_TAC>>
  simp[Once replace_last_def,SimpRHS]
QED

Theorem strip_term_line_last:
  strip_term_line ss =
  case ss of [] => NONE
  | (x::xs) =>
    case term_last ss of
      NONE => NONE
    | SOME t => SOME (replace_last x xs t)
Proof
  Cases_on`ss`>>
  simp[strip_term_line_def,strip_term_line_aux_def,strip_term_line_aux_last]
QED

(*
  EVAL ``strip_term_line (toks «foo bar aaa;»)``
  EVAL ``strip_term_line (toks «foo bar bbb ;»)``
  EVAL ``strip_term_line (toks «foo bar ~1;»)``
  EVAL ``strip_term_line (toks «foo bar 1 ;»)``
*)

Definition parse_op_def:
  parse_op cmp =
  if cmp = «>=» then SOME (RIneq GreaterEqual)
  else if cmp = «=» then SOME REq
  else if cmp = «>» then SOME (RIneq Greater)
  else if cmp = «<=» then SOME (RIneq LessEqual)
  else if cmp = «<» then SOME (RIneq Less)
  else NONE
End

Definition is_arrow_def:
  is_arrow s ⇔ s = «==>» ∨ s = «<==» ∨ s = «<==>»
End

(* No arrow may also be a comparison. parse_pbc_rest's unreified
  path matches INL cmp :: INR deg :: rest, so were an arrow to parse as a
  comparison it would accept a line whose comparison token is an arrow —
  e.g. a preserved_add whose preserved variable is missing. *)
Theorem parse_op_arrow:
  ∀s. is_arrow s ⇒ parse_op s = NONE
Proof
  rw[is_arrow_def]>>EVAL_TAC
QED

(* Scan a non-empty guard of bare literals terminated by an arrow.
  NONE means the line has no reification, so its prefix is a linear term. *)
Definition parse_reif_aux_def:
  (parse_reif_aux [] acc = NONE) ∧
  (parse_reif_aux (INR n::rest) acc = NONE) ∧
  (parse_reif_aux (INL s::rest) acc =
    if is_arrow s then
      (if acc = [] then NONE else SOME (s,REVERSE acc,rest))
    else
      case parse_lit s of
        NONE => NONE
      | SOME l => parse_reif_aux rest (l::acc))
End

(* Bwd and Iff take a pbop, so REq has no head here, and a single
  literal, so a longer guard has no head either *)
Definition mk_hd_def:
  mk_hd arrow ls rel =
  if arrow = «==>» then SOME (Fwd ls rel)
  else
    case rel of
      REq => NONE
    | RIneq op =>
      (case ls of [l] =>
        if arrow = «<==» then SOME (Bwd l op)
        else if arrow = «<==>» then SOME (Iff l op)
        else NONE
      | _ => NONE)
End

Definition parse_constraint_def:
  parse_constraint line =
  case strip_term_line line of
    NONE => NONE
  | SOME ls =>
    let (arrow,gs,body) =
      (case parse_reif_aux ls [] of
        NONE => («==>»,[],ls)
      | SOME (arrow,gs,rest) => (arrow,gs,rest)) in
    (case parse_constraint_LHS body of (rest,lhs) =>
      (case rest of
        [INL cmp; INR deg] =>
        (case parse_op cmp of
          NONE => NONE
        | SOME rel =>
          (case mk_hd arrow gs rel of
            NONE => NONE
          | SOME hd => SOME ((hd,lhs,deg):mlstring pbc)))
      | _ => NONE))
End

(* strips off the head of a line as a list of annotations *)
Definition parse_annot_def:
  parse_annot line =
  case line of
    (INL s)::ls =>
    if strlen s ≥ 1 ∧ strsub_unsafe s 0 = #"@" then
      (let (annots,rest) = parse_annot ls in
        (substring s 1 (strlen s - 1)::annots, rest))
    else ([], line)
  | _ => ([], line)
End

Definition parse_annot_constraint_def:
  parse_annot_constraint line =
  case parse_annot line of (annot,line) =>
    OPTION_MAP (λres. (annot,res)) (parse_constraint line)
End

(*
  EVAL ``parse_annot (toks «2 ~x1 1 ~x3 >= 1;»)``;
  EVAL ``parse_constraint (toks «2 ~x1 1 ~x3 >= 1 ;»)``;
  EVAL ``parse_annot_constraint (toks «@aaa 2 ~x1 1 ~x3 >= 1;»)``;
  EVAL ``parse_annot_constraint (toks «@aaa @bbb 2 ~x1 1 ~x3 >= 1;»)``;

  Reification, and the constraints each form normalises to. The body is
  normalised first, so the big-M coefficient is its degree, and a
  constraint whose degree is not positive gains no guard terms. In the
  npbc output a negative coefficient denotes a negated literal.

  EVAL ``parse_constraint (toks «z1 z2 ~z3 ==> +1 x1 +2 x2 >= 2;»)``;
  EVAL ``parse_constraint (toks «z1 <== 1 x1 <= 5;»)``;
  EVAL ``parse_constraint (toks «z1 <==> 1 x1 > 3;»)``;
  EVAL ``parse_constraint (toks «==> 1 x1 >= 1;»)``;              (* NONE: empty guard *)
  EVAL ``parse_constraint (toks «z1 z2 <== 1 x1 >= 1;»)``;        (* NONE: <== takes one literal *)

  EVAL ``MAP inject (to_gnpbc
    (Fwd [Pos 1;Pos 2;Neg 3] (RIneq GreaterEqual),[(1,Pos 4);(2,Pos 5)],2))``;
      [([(-2,1); (-2,2); (2,3); (1,4); (2,5)],2)]
  EVAL ``MAP inject (to_gnpbc
    (Fwd [Pos 1] (RIneq GreaterEqual),[(3,Pos 4);(2,Neg 4)],3))``;
      [([(-1,1); (1,4)],1)]                  (* 3 x1 2 ~x1 compacts to 1 x1 first *)
  EVAL ``MAP inject (to_gnpbc
    (Fwd [Pos 1;Pos 2] (RIneq GreaterEqual),[(1,Pos 4)],-1))``;
      [([(1,4)],-1)]                         (* already trivial, no guard added *)
  EVAL ``MAP inject (to_gnpbc
    (Fwd [Pos 4] (RIneq GreaterEqual),[(1,Pos 4)],1))``;
      [([],0)]                               (* guard is the constraint's own var *)
  EVAL ``MAP inject (to_gnpbc
    (Bwd (Pos 1) LessEqual,[(1,Pos 4)],9223372036854775807))``;
      [([(9223372036854775808,1); (1,4)],9223372036854775808)]
  EVAL ``MAP inject (to_gnpbc
    (Fwd [Pos 1;Pos 2;Neg 3] REq,[(1,Pos 4)],2))``;
      [([(-2,1); (-2,2); (2,3); (1,4)],2); ([(-1,4)],-1)]
  EVAL ``MAP inject (to_gnpbc
    (Iff (Pos 1) GreaterEqual,[(1,Pos 4);(1,Pos 5)],1))``;
      the forward constraint, then the backward one
*)

Definition parse_constraints_def:
  (parse_constraints [] acc = SOME (REVERSE acc)) ∧
  (parse_constraints (s::ss) acc =
    case parse_annot_constraint s of
      NONE => NONE
    | SOME pbc => parse_constraints ss (pbc::acc))
End

Definition nocomment_line_def:
  (nocomment_line (INL c::cs) =
    (strlen c < 1 ∨ strsub_unsafe c 0 ≠ #"*")) ∧
  (nocomment_line _ = T)
End

(* Allow the min objective to end with either a constant or not:
  lin_term constant
  lin_term
*)

(* parse objective term in pbc ... (; stripped) *)
Definition parse_obj_term_def:
  parse_obj_term xs =
  case parse_constraint_LHS xs of (rest,obj) =>
  case rest of
    [] => SOME (obj,0:int)
  | [INR c] => SOME (obj,c:int)
  | _ => NONE
End

(* parse objective line in PBF *)
Definition parse_obj_def:
  (parse_obj [] = NONE) ∧
  (parse_obj (x::xs) =
    if x = INL «min:» then
      OPTION_BIND (strip_term_line xs) parse_obj_term
    else NONE
  )
End

(*
  EVAL``parse_obj (toks «min: 1 ~x199 1 x2 ~5 ;»)``
  EVAL``parse_obj (toks «min: 1 ~x199 1 x2 ~5;»)``
  EVAL``parse_obj (toks «min: 1 ~x199 1 x2 ;»)``
  EVAL``parse_obj (toks «min: 1 ~x199 1 x2;»)``
  EVAL``parse_obj (toks «min: 1 ~x199 1 x2 5;»)``
*)

(* raw string but must be a valid var name *)
Definition parse_var_raw_def:
  (parse_var_raw (INL s) =
    if goodString s then SOME s else NONE) ∧
  (parse_var_raw _ = NONE)
End

Definition parse_vars_raw_def:
  (parse_vars_raw [] = SOME []) ∧
  (parse_vars_raw (s::ss) =
    case parse_var_raw s of NONE => NONE | SOME v =>
    case parse_vars_raw ss of NONE => NONE | SOME vs => SOME (v::vs))
End

(* parse projection or preserved line in PBF *)
Definition parse_pres_def:
  (parse_pres [] = NONE) ∧
  (parse_pres (x::xs) =
    if x = INL «preserved:» then
      OPTION_BIND (strip_term_line xs) parse_vars_raw
    else NONE)
End

(*
  EVAL``parse_pres (toks «preserved: x1 x2 x2 a b c ;»)``
  EVAL``parse_pres (toks «preserved: x1 x2 x2 a b c;»)``
*)

(* parse optional objective line *)
Definition parse_obj_maybe_def:
  (parse_obj_maybe [] = (NONE , [])) ∧
  (parse_obj_maybe (l::ls) =
  case parse_obj l of
    NONE => (NONE, l::ls)
  | SOME obj => (SOME obj, ls))
End

(* parse optional preserved line *)
Definition parse_pres_maybe_def:
  (parse_pres_maybe [] = (NONE , [])) ∧
  (parse_pres_maybe (l::ls) =
  case parse_pres l of
    NONE => (NONE, l::ls)
  | SOME pres => (SOME pres, ls))
End

Definition parse_obj_pres_maybe_def:
  parse_obj_pres_maybe ls =
    case parse_obj_maybe ls of
    | (SOME obj,ls) =>
        (SOME obj, parse_pres_maybe ls)
    | (NONE, ls) =>
      (case parse_pres_maybe ls of
      | (SOME pres,ls) =>
        (case parse_obj_maybe ls of (ob,ls) => (ob, SOME pres, ls))
      | (NONE,ls) => (NONE,NONE,ls))
End

(* Parse the tokenized pbf file *)
Definition parse_pbf_toks_def:
  parse_pbf_toks tokss =
  let nocomments = FILTER nocomment_line tokss in
  let (obj,pres,rest) = parse_obj_pres_maybe nocomments in
  case parse_constraints rest [] of
    NONE => NONE
  | SOME pbf => SOME (pres,obj,pbf)
End

(* Parse a list of strings in annotated pbf format *)
Definition parse_pbf_def:
  parse_pbf strs = parse_pbf_toks (MAP toks strs)
End

(*
  Parsing an OPB file one line at a time, numbering and normalising
  each constraint as it is read
*)

(* Drops the annotations at the head of a line *)
Definition skip_annot_def:
  skip_annot line =
  case line of
    (INL s)::ls =>
    if strlen s ≥ 1 ∧ strsub_unsafe s 0 = #"@" then skip_annot ls
    else line
  | _ => line
End

Theorem skip_annot_thm:
  ∀line. skip_annot line = SND (parse_annot line)
Proof
  ho_match_mp_tac skip_annot_ind>>
  rw[]>>
  simp[Once skip_annot_def,Once parse_annot_def]>>
  rpt (TOP_CASE_TAC>>gvs[])>>
  pairarg_tac>>
  gvs[]
QED

(* The guard and linear term of a line, and the unparsed remainder *)
Definition parse_constraint_front_def:
  parse_constraint_front ls =
  let (arrow,gs,body) =
    (case parse_reif_aux ls [] of
      NONE => («==>»,[],ls)
    | SOME (arrow,gs,rest) => (arrow,gs,rest)) in
  case parse_constraint_LHS body of (rest,lhs) => (arrow,gs,lhs,rest)
End

(* The comparison and degree ending a line, including its ; terminator *)
Definition parse_cmp_deg_def:
  parse_cmp_deg rest =
  case rest of
    [INL cmp; INR deg; INL t] =>
      if t = «;» then SOME (cmp,deg:int) else NONE
  | [INL cmp; INL s] =>
      (case strip_term s of
        NONE => NONE
      | SOME d =>
        (case tokenize d of
          INR deg => SOME (cmp,deg)
        | INL _ => NONE))
  | _ => NONE
End

(* parse_constraint on a line that still has its terminator *)
Definition parse_constraint_ns_def:
  parse_constraint_ns line =
  case parse_constraint_front line of (arrow,gs,lhs,rest) =>
  case parse_cmp_deg rest of
    NONE => NONE
  | SOME (cmp,deg) =>
    (case parse_op cmp of
      NONE => NONE
    | SOME rel =>
      (case mk_hd arrow gs rel of
        NONE => NONE
      | SOME hd => SOME ((hd,lhs,deg):mlstring pbc)))
End

Theorem strip_term_line_SNOC[local]:
  ∀xs acc t.
    strip_term_line_aux (xs ++ [t]) acc =
    case t of
      INR n => NONE
    | INL s =>
      if s = «;» then SOME (REVERSE acc ++ xs)
      else
        case strip_term s of
          NONE => NONE
        | SOME d => SOME (REVERSE acc ++ xs ++ [tokenize d])
Proof
  Induct
  >- rw[strip_term_line_aux_def]>>
  rw[]>>
  Cases_on`xs`>>
  gvs[strip_term_line_aux_def]>>
  rewrite_tac[GSYM APPEND_ASSOC,APPEND]
QED

(* A token carrying the terminator is neither a literal nor an arrow *)
Theorem strip_term_inert[local]:
  strip_term s = SOME d ⇒ parse_lit s = NONE ∧ ¬is_arrow s
Proof
  simp[strip_term_def]>>
  strip_tac>>
  `¬goodChar #";"` by EVAL_TAC>>
  namedCases_on`s`["l"]>>
  gvs[parse_lit_def,goodString_eq_EVERY_goodChar,
      mlstringTheory.strsub_unsafe_eq_strsub]>>
  `¬EVERY goodChar l` by (
    simp[EXISTS_MEM,MEM_EL]>>
    qexists_tac`#";"`>>
    simp[]>>
    qexists_tac`STRLEN l − 1`>>
    simp[])>>
  `STRLEN l ≥ 2 ⇒
   ¬EVERY goodChar (explode (substring (implode l) 1 (STRLEN l − 1)))` by (
    strip_tac>>
    simp[mlstringTheory.substring_def,SEG_TAKE_DROP,EXISTS_MEM,MEM_EL]>>
    qexists_tac`#";"`>>
    simp[]>>
    qexists_tac`STRLEN l − 2`>>
    simp[EL_TAKE,EL_DROP])>>
  rw[is_arrow_def]>>
  strip_tac>>
  gvs[]
QED

Theorem parse_constraint_LHS_aux_SNOC[local]:
  ∀xs acc.
    (∀s. t = INL s ⇒ parse_lit s = NONE) ⇒
    parse_constraint_LHS_aux (xs ++ [t]) acc =
    (FST (parse_constraint_LHS_aux xs acc) ++ [t],
     SND (parse_constraint_LHS_aux xs acc))
Proof
  ho_match_mp_tac parse_constraint_LHS_aux_ind>>
  rw[]>>
  Cases_on`t`>>
  gvs[parse_constraint_LHS_aux_def]>>
  TOP_CASE_TAC>>
  gvs[]
QED

Theorem parse_reif_aux_SNOC[local]:
  ∀xs acc.
    (∀s. t = INL s ⇒ parse_lit s = NONE ∧ ¬is_arrow s) ⇒
    parse_reif_aux (xs ++ [t]) acc =
    OPTION_MAP (λ(arrow,gs,rest). (arrow,gs,rest ++ [t]))
      (parse_reif_aux xs acc)
Proof
  ho_match_mp_tac parse_reif_aux_ind>>
  rw[]>>
  Cases_on`t`>>
  gvs[parse_reif_aux_def]>>
  rw[]>>
  TOP_CASE_TAC>>
  gvs[]
QED

Theorem parse_constraint_LHS_aux_suffix[local]:
  ∀xs acc rest lhs.
    parse_constraint_LHS_aux xs acc = (rest,lhs) ⇒
    ∃pre. xs = pre ++ rest
Proof
  ho_match_mp_tac parse_constraint_LHS_aux_ind>>
  rw[parse_constraint_LHS_aux_def]>>
  gvs[AllCaseEqs()]
QED

Theorem parse_reif_aux_suffix[local]:
  ∀xs acc arrow gs rest.
    parse_reif_aux xs acc = SOME (arrow,gs,rest) ⇒
    ∃pre. xs = pre ++ rest
Proof
  ho_match_mp_tac parse_reif_aux_ind>>
  rw[parse_reif_aux_def]>>
  gvs[AllCaseEqs()]
QED

Theorem parse_constraint_front_SNOC[local]:
  (∀s. t = INL s ⇒ parse_lit s = NONE ∧ ¬is_arrow s) ∧
  parse_constraint_front xs = (arrow,gs,lhs,rest) ⇒
  parse_constraint_front (xs ++ [t]) = (arrow,gs,lhs,rest ++ [t])
Proof
  strip_tac>>
  drule parse_reif_aux_SNOC>>
  `∀s. t = INL s ⇒ parse_lit s = NONE` by simp[]>>
  drule parse_constraint_LHS_aux_SNOC>>
  rpt strip_tac>>
  gvs[parse_constraint_front_def,parse_constraint_LHS_def]>>
  Cases_on`parse_reif_aux xs []`>>
  gvs[]
  >- (
    Cases_on`parse_constraint_LHS_aux xs []`>>
    gvs[])>>
  rename1`SOME p`>>
  PairCases_on`p`>>
  gvs[]>>
  Cases_on`parse_constraint_LHS_aux p2 []`>>
  gvs[]
QED

Theorem parse_constraint_front_suffix[local]:
  parse_constraint_front xs = (arrow,gs,lhs,rest) ⇒
  ∃pre. xs = pre ++ rest
Proof
  rw[parse_constraint_front_def,parse_constraint_LHS_def]>>
  Cases_on`parse_reif_aux xs []`>>
  gvs[]
  >- (
    Cases_on`parse_constraint_LHS_aux xs []`>>
    gvs[]>>
    drule parse_constraint_LHS_aux_suffix>>
    simp[])>>
  rename1`SOME p`>>
  PairCases_on`p`>>
  gvs[]>>
  Cases_on`parse_constraint_LHS_aux p2 []`>>
  gvs[]>>
  drule parse_reif_aux_suffix>>
  drule parse_constraint_LHS_aux_suffix>>
  metis_tac[APPEND_ASSOC]
QED

Theorem parse_cmp_deg_eq_SOME[local]:
  parse_cmp_deg rest = SOME (cmp,deg) ⇔
  rest = [INL cmp; INR deg; INL «;»] ∨
  ∃s d. rest = [INL cmp; INL s] ∧
    strip_term s = SOME d ∧ tokenize d = INR deg
Proof
  simp[parse_cmp_deg_def,AllCaseEqs()]>>
  eq_tac>>
  rw[]>>
  simp[]
QED

(* Stripping the terminator first and recognising it last agree *)
Theorem parse_constraint_front_strip[local]:
  (∃ls. strip_term_line line = SOME ls ∧
    parse_constraint_front ls = (arrow,gs,lhs,[INL cmp; INR deg])) ⇔
  (∃rest. parse_constraint_front line = (arrow,gs,lhs,rest) ∧
    parse_cmp_deg rest = SOME (cmp,deg))
Proof
  simp[strip_term_line_def,parse_cmp_deg_eq_SOME]>>
  qspec_then`line` strip_assume_tac SNOC_CASES>>
  gvs[SNOC_APPEND]
  >- (
    simp[strip_term_line_aux_def,parse_constraint_front_def,
      parse_reif_aux_def,parse_constraint_LHS_def,
      parse_constraint_LHS_aux_def])>>
  rename1`parse_constraint_front (front ++ [t])`>>
  simp[strip_term_line_SNOC]>>
  eq_tac>>
  strip_tac
  >- (
    Cases_on`t`>>
    gvs[]>>
    rename1`INL s`>>
    Cases_on`s = «;»`>>
    gvs[]
    >- (
      `strip_term «;» = SOME «»` by EVAL_TAC>>
      drule strip_term_inert>>
      strip_tac>>
      drule_at Any parse_constraint_front_SNOC>>
      disch_then(qspec_then`INL «;»` mp_tac)>>
      simp[])>>
    gvs[AllCaseEqs()]>>
    `tokenize d = INR deg` by (
      drule parse_constraint_front_suffix>>
      strip_tac>>
      pop_assum (mp_tac o Q.AP_TERM `LAST`)>>
      simp[LAST_APPEND_CONS])>>
    `∃a g lh r. parse_constraint_front front = (a,g,lh,r)` by
      metis_tac[PAIR]>>
    drule_at Any parse_constraint_front_SNOC>>
    disch_then(qspec_then`INR deg` mp_tac)>>
    gvs[]>>
    strip_tac>>
    gvs[]>>
    qpat_x_assum`parse_constraint_front (_ ++ _) = _` kall_tac>>
    drule strip_term_inert>>
    strip_tac>>
    drule_at Any parse_constraint_front_SNOC>>
    disch_then(qspec_then`INL s` mp_tac)>>
    simp[])
  >- (
    `t = INL «;»` by (
      drule parse_constraint_front_suffix>>
      strip_tac>>
      pop_assum (mp_tac o Q.AP_TERM `LAST`)>>
      simp[LAST_APPEND_CONS])>>
    `strip_term «;» = SOME «»` by EVAL_TAC>>
    drule strip_term_inert>>
    strip_tac>>
    `∃a g lh r. parse_constraint_front front = (a,g,lh,r)` by
      metis_tac[PAIR]>>
    drule_at Any parse_constraint_front_SNOC>>
    disch_then(qspec_then`INL «;»` mp_tac)>>
    gvs[])>>
  `t = INL s` by (
    drule parse_constraint_front_suffix>>
    strip_tac>>
    pop_assum (mp_tac o Q.AP_TERM `LAST`)>>
    simp[LAST_APPEND_CONS])>>
  `s ≠ «;»` by (
    strip_tac>>
    `strip_term «;» = SOME «» ∧ tokenize «» = INL «»` by EVAL_TAC>>
    gvs[])>>
  gvs[]>>
  drule strip_term_inert>>
  strip_tac>>
  `∃a g lh r. parse_constraint_front front = (a,g,lh,r)` by
    metis_tac[PAIR]>>
  drule_at Any parse_constraint_front_SNOC>>
  disch_then (fn th =>
    qspec_then`INL s` mp_tac th>>
    qspec_then`INR deg` mp_tac th)>>
  gvs[]
QED

Theorem parse_constraint_eq_SOME[local]:
  parse_constraint line = SOME c ⇔
  ∃ls arrow gs lhs cmp deg rel hd.
    strip_term_line line = SOME ls ∧
    parse_constraint_front ls = (arrow,gs,lhs,[INL cmp; INR deg]) ∧
    parse_op cmp = SOME rel ∧ mk_hd arrow gs rel = SOME hd ∧
    c = (hd,lhs,deg)
Proof
  simp[parse_constraint_def,parse_constraint_front_def]>>
  Cases_on`strip_term_line line`>>
  simp[]>>
  pairarg_tac>>
  simp[]>>
  Cases_on`parse_constraint_LHS body`>>
  simp[AllCaseEqs()]>>
  eq_tac>>
  rw[]>>
  simp[]
QED

Theorem parse_constraint_ns_thm:
  ∀line. parse_constraint_ns line = parse_constraint line
Proof
  rw[]>>
  qsuff_tac`∀c. parse_constraint_ns line = SOME c ⇔
    parse_constraint line = SOME c`
  >- (
    Cases_on`parse_constraint_ns line`>>
    Cases_on`parse_constraint line`>>
    gvs[])>>
  rw[]>>
  simp[parse_constraint_eq_SOME,parse_constraint_ns_def,AllCaseEqs(),
    PULL_EXISTS]>>
  eq_tac>>
  strip_tac>>
  gvs[]
  >- (
    `∃ls. strip_term_line line = SOME ls ∧
      parse_constraint_front ls = (arrow,gs,lhs,[INL cmp; INR deg])` by
      simp[parse_constraint_front_strip]>>
    simp[])>>
  `∃rest. parse_constraint_front line = (arrow,gs,lhs,rest) ∧
    parse_cmp_deg rest = SOME (cmp,deg)` by
    simp[GSYM parse_constraint_front_strip]>>
  simp[]
QED

(* acc holds the normalised constraints so far, in reverse *)
Definition parse_norm_line_def:
  parse_norm_line l s acc =
  case parse_constraint_ns (skip_annot l) of
    NONE => NONE
  | SOME c => SOME (name_norm_pbc c s acc)
End

Definition parse_norm_lines_def:
  (parse_norm_lines [] s acc = SOME (acc,s)) ∧
  (parse_norm_lines (l::ls) s acc =
    if nocomment_line l then
      case parse_norm_line l s acc of
        NONE => NONE
      | SOME (acc1,s1) => parse_norm_lines ls s1 acc1
    else parse_norm_lines ls s acc)
End

Definition opt_list_def:
  opt_list NONE = [] ∧
  opt_list (SOME x) = [x]
End

(* The objective and preserved lines are among the first two lines l1, l2.
  Whatever they leave over is a constraint. *)
Definition split_header_def:
  split_header l1 l2 = parse_obj_pres_maybe (opt_list l1 ++ opt_list l2)
End

Definition parse_norm_header_def:
  parse_norm_header l1 l2 s =
  let (obj,pres,rest) = split_header l1 l2 in
  let (pres',s') = name_to_num_pres pres s in
  let (obj',s'') = name_to_num_obj obj s' in
  case parse_norm_lines rest s'' [] of
    NONE => NONE
  | SOME (acc,t) =>
    SOME (OPTION_MAP list_to_num_set pres',normalise_obj obj',acc,t)
End

Definition parse_norm_pbf_toks_def:
  parse_norm_pbf_toks tokss s =
  let nocomments = FILTER nocomment_line tokss in
  case parse_norm_header (oHD nocomments) (oHD (DROP 1 nocomments)) s of
    NONE => NONE
  | SOME (pres,obj,acc,s1) =>
    (case parse_norm_lines (DROP 2 nocomments) s1 acc of
      NONE => NONE
    | SOME (acc1,t) => SOME ((pres,obj,REVERSE acc1),t))
End

Theorem parse_norm_lines_thm:
  ∀ls s acc.
    OPTION_MAP (REVERSE ## I) (parse_norm_lines ls s acc) =
    OPTION_MAP (λafml. name_norm_pbf (MAP SND afml) s acc)
      (OPT_MMAP parse_annot_constraint (FILTER nocomment_line ls))
Proof
  Induct>>
  rw[parse_norm_lines_def,name_norm_pbf_def,OPT_MMAP_def]>>
  simp[parse_norm_line_def,parse_annot_constraint_def,skip_annot_thm,
    parse_constraint_ns_thm]>>
  Cases_on`parse_annot h`>>
  rename1`parse_annot h = (annot,line)`>>
  gvs[]>>
  Cases_on`parse_constraint line`>>
  gvs[]>>
  rename1`name_norm_pbc c s acc`>>
  Cases_on`name_norm_pbc c s acc`>>
  rename1`name_norm_pbc c s acc = (acc1,s1)`>>
  gvs[]>>
  Cases_on`OPT_MMAP parse_annot_constraint (FILTER nocomment_line ls)`>>
  gvs[name_norm_pbf_def]
QED

Theorem parse_norm_lines_FILTER:
  ∀ls s acc.
    parse_norm_lines (FILTER nocomment_line ls) s acc =
    parse_norm_lines ls s acc
Proof
  Induct>>
  rw[parse_norm_lines_def]
QED

Theorem parse_constraints_OPT_MMAP[local]:
  ∀ls acc.
    parse_constraints ls acc =
    OPTION_MAP (λr. REVERSE acc ++ r) (OPT_MMAP parse_annot_constraint ls)
Proof
  Induct>>
  rw[parse_constraints_def,OPT_MMAP_def]>>
  Cases_on`parse_annot_constraint h`>>
  simp[]>>
  Cases_on`OPT_MMAP parse_annot_constraint ls`>>
  simp[]
QED

Theorem parse_norm_lines_APPEND[local]:
  ∀xs s acc.
    parse_norm_lines (xs ++ ys) s acc =
    case parse_norm_lines xs s acc of
      NONE => NONE
    | SOME (acc1,s1) => parse_norm_lines ys s1 acc1
Proof
  Induct>>
  rw[parse_norm_lines_def]>>
  rpt (TOP_CASE_TAC>>gvs[])
QED

(* The objective and preserved lines are among the first two lines *)
Theorem parse_obj_pres_maybe_TAKE[local]:
  parse_obj_pres_maybe ls = (obj,pres,rest) ⇒
  (∀P. EVERY P ls ⇒ EVERY P rest) ∧
  ∃hrest.
    parse_obj_pres_maybe (TAKE 2 ls) = (obj,pres,hrest) ∧
    rest = hrest ++ DROP 2 ls
Proof
  Cases_on`ls`
  >- (
    EVAL_TAC>>
    rw[])>>
  rename1`l1::tl`>>
  Cases_on`tl`>>
  simp[parse_obj_pres_maybe_def,parse_obj_maybe_def,parse_pres_maybe_def]
  >- (
    Cases_on`parse_obj l1`>>
    Cases_on`parse_pres l1`>>
    rw[parse_obj_maybe_def,parse_pres_maybe_def]>>
    simp[])>>
  rename1`l1::l2::t`>>
  Cases_on`parse_obj l1`>>
  Cases_on`parse_pres l1`>>
  Cases_on`parse_obj l2`>>
  Cases_on`parse_pres l2`>>
  rw[parse_obj_maybe_def,parse_pres_maybe_def]>>
  simp[parse_obj_maybe_def,parse_pres_maybe_def]
QED

Theorem parse_obj_pres_maybe_EVERY:
  parse_obj_pres_maybe ls = (obj,pres,rest) ∧ EVERY P ls ⇒ EVERY P rest
Proof
  metis_tac[parse_obj_pres_maybe_TAKE]
QED

Theorem split_header_oHD:
  split_header (oHD ls) (oHD (DROP 1 ls)) = parse_obj_pres_maybe (TAKE 2 ls)
Proof
  Cases_on`ls`>>
  simp[split_header_def,opt_list_def]>>
  Cases_on`t`>>
  simp[opt_list_def]
QED

Theorem parse_norm_pbf_toks_thm:
  parse_norm_pbf_toks tokss s =
  OPTION_MAP (λprob. name_norm_prob (strip_annot_prob prob) s)
    (parse_pbf_toks tokss)
Proof
  simp[parse_norm_pbf_toks_def,parse_pbf_toks_def,parse_norm_header_def,
       split_header_oHD]>>
  qabbrev_tac`fl = FILTER nocomment_line tokss`>>
  `EVERY nocomment_line fl` by simp[Abbr`fl`,EVERY_FILTER]>>
  `∃obj pres rest. parse_obj_pres_maybe fl = (obj,pres,rest)` by
    metis_tac[PAIR]>>
  drule parse_obj_pres_maybe_TAKE>>
  strip_tac>>
  simp[]>>
  `EVERY nocomment_line (hrest ++ DROP 2 fl)` by metis_tac[]>>
  `FILTER nocomment_line (hrest ++ DROP 2 fl) = hrest ++ DROP 2 fl` by
    metis_tac[FILTER_EQ_ID]>>
  Cases_on`name_to_num_pres pres s`>>
  rename1`name_to_num_pres pres s = (pres1,s1)`>>
  Cases_on`name_to_num_obj obj s1`>>
  rename1`name_to_num_obj obj s1 = (obj1,s2)`>>
  simp[parse_constraints_OPT_MMAP]>>
  qspecl_then [`hrest ++ DROP 2 fl`,`s2`,`[]`] mp_tac parse_norm_lines_thm>>
  simp[parse_norm_lines_APPEND]>>
  Cases_on`OPT_MMAP parse_annot_constraint (hrest ++ DROP 2 fl)`>>
  simp[]>>
  rpt (TOP_CASE_TAC>>gvs[])>>
  strip_tac>>
  simp[name_norm_prob_def,strip_annot_prob_def]
QED

(*
  Parsing a proof file
*)

Definition is_numeric_def:
  is_numeric c =
  let n = ORD c in
  48 ≤ n ∧ n ≤ 57
End

Definition is_num_prefix_def:
  is_num_prefix c =
  (c = #"-" ∨ c = #"+" ∨ c = #"~")
End

(* parse as integers, except if it ends with ; *)
Definition int_start_def:
  int_start s =
  if strlen s > 0
  then
    if strsub_unsafe s (strlen s - 1) = #";" then F
    else
      is_numeric (strsub_unsafe s 0) ∨
      (strlen s > 1 ∧
      is_num_prefix (strsub_unsafe s 0) ∧
      is_numeric (strsub_unsafe s 1))
  else
    F
End

Theorem fromChars_not_digits[local]:
  ∀str.
    str = [] ∨ ¬EVERY isDigit str ⇒
    mlint$fromChars (STRLEN str) (strlit str) = NONE
Proof
  Cases
  >- simp [mlintTheory.fromChars_def]
  \\ rename1 ‘STRING c cs’
  \\ qspecl_then [‘SUC (STRLEN cs)’,‘strlit (STRING c cs)’] mp_tac
       mlintTheory.fromChars_IS_SOME_IFF
  \\ simp []
  \\ Cases_on ‘fromChars (SUC (STRLEN cs)) (implode (STRING c cs))’
  \\ simp [EXISTS_MEM,EVERY_MEM]
  \\ metis_tac []
QED

Theorem fromString_int_start[local]:
  ¬int_start s ⇒ mlint$fromString s = NONE
Proof
  Cases_on ‘s’
  \\ rename1 ‘strlit l’
  \\ Cases_on ‘l’
  >- EVAL_TAC
  \\ rename1 ‘strlit (c::cs)’
  \\ ‘∀ch. substring (implode (STRING ch cs)) 1 (STRLEN cs) = strlit cs’ by (
    simp [mlstringTheory.substring_def]
    \\ simp_tac bool_ss [ONE,SEG_SUC_CONS,SEG_LENGTH_ID])
  \\ ‘(STRING c cs)❲STRLEN cs❳ = #";" ⇒
      ¬EVERY isDigit (STRING c cs) ∧ (cs ≠ "" ⇒ ¬EVERY isDigit cs)’ by (
    strip_tac
    \\ ‘¬isDigit #";"’ by EVAL_TAC
    \\ rewrite_tac [EVERY_EL]
    \\ conj_tac
    >- (simp [] \\ qexists_tac ‘STRLEN cs’ \\ simp [])
    \\ Cases_on ‘cs’
    \\ fs []
    \\ rename1 ‘STRING d ds’
    \\ qexists_tac ‘STRLEN ds’
    \\ simp [])
  \\ qspec_then ‘cs’ mp_tac fromChars_not_digits
  \\ qspec_then ‘STRING c cs’ mp_tac fromChars_not_digits
  \\ Cases_on ‘cs’
  \\ fs [int_start_def,mlintTheory.fromString_def,is_numeric_def,
         is_num_prefix_def,isDigit_def,mlstringTheory.strsub_unsafe_eq_strsub]
  \\ rpt strip_tac
  \\ rpt IF_CASES_TAC
  \\ gvs []
QED

Theorem tokenize_eq:
  tokenize s =
  if int_start s then
    case mlint$fromString s of
      NONE => INL s
    | SOME i => INR i
  else INL s
Proof
  rw [tokenize_def]
  \\ drule fromString_int_start
  \\ simp []
QED

(*
  Parsing a proof file, one line at a time.

  parse_line reads a line into a pline over names; name_pline numbers its
  names (the table in npbc_parseProg implements it); fin_lstep and
  fin_cstep turn the numbered line into the step it states.
*)

Definition binopc_def:
  binopc stack =
  case stack of
    Id a::b::rest => SOME (a,b,rest)
  | _ => NONE
End

(* Parsing cutting planes in polish notation (header "pol", ";" stripped) *)
Definition parse_cutting_aux_def:
  (parse_cutting_aux (x::xs) (stack:mlstring constr list) =
  case x of INR n =>
    if n ≥ 0 then
      parse_cutting_aux xs (Id (Num n) :: stack)
    else NONE
  | INL s =>
  if strlen s = 1
  then
    let c = strsub_unsafe s 0 in
      if c = #"+" then
        (case stack of
          a::b::rest => parse_cutting_aux xs (Add b a::rest)
        | _ => NONE)
      else if c = #"*" then
        (case binopc stack of NONE => NONE
        | SOME (a,b,rest) => parse_cutting_aux xs (Mul b a::rest))
      else if c = #"w" then
        (case stack of
          Lit (Pos v)::a::rest => parse_cutting_aux xs (Weak a [v]::rest)
        | _ => NONE)
      else if c = #"s" then
        (case stack of
          a::rest => parse_cutting_aux xs (Sat a::rest)
        | _ => NONE)
     else if c = #"c" then
      (case binopc stack of NONE => NONE
      | SOME (a,b,rest) => parse_cutting_aux xs (Div Cd b a::rest))
     else if c = #"d" then
      (case binopc stack of NONE => NONE
      | SOME (a,b,rest) => parse_cutting_aux xs (Div Dd b a::rest))
     else if c = #"m" then
      (case binopc stack of NONE => NONE
      | SOME (a,b,rest) => parse_cutting_aux xs (Div Md b a::rest))
     else if c = #"n" then
      (case binopc stack of NONE => NONE
      | SOME (a,b,rest) => parse_cutting_aux xs (Div Nd b a::rest))
     else if c = #"-" then
      (case binopc stack of NONE => NONE
      | SOME (a,b,rest) => parse_cutting_aux xs (Minus b a::rest))
     else
      (case parse_lit s of
      | SOME l => parse_cutting_aux xs (Lit l::stack)
      | NONE => NONE)
  else
    case parse_lit s of
    | SOME l => parse_cutting_aux xs (Lit l::stack)
    | NONE => NONE) ∧
  (parse_cutting_aux [] [c] = SOME c) ∧
  (parse_cutting_aux [] _ = NONE)
End

Definition parse_cutting_def:
  parse_cutting ls = parse_cutting_aux ls []
End

(*
  EVAL ``parse_cutting (toks «8 2 + 3 + 1 s + 9 2 n + x5 2 * + 5 -»)``;
*)

(* A proof-file constraint and the tokens after its degree *)
Definition parse_pbc_rest_def:
  parse_pbc_rest line =
  case parse_constraint_front line of (arrow,gs,lhs,rest) =>
  case rest of
    INL cmp :: INR deg :: rest' =>
    (case parse_op cmp of
      NONE => NONE
    | SOME rel =>
      (case mk_hd arrow gs rel of
        NONE => NONE
      | SOME hd => SOME (((hd,lhs,deg):mlstring pbc),rest')))
  | _ => NONE
End

(* A rup hint must be a sequence of numbers *)
Definition strip_rup_hint_aux_def:
  (strip_rup_hint_aux [] acc = SOME (REVERSE acc)) ∧
  (strip_rup_hint_aux (x::xs) acc =
  case x of INR n =>
    if n ≥ 0 then
      strip_rup_hint_aux xs (Num n::acc)
    else NONE
  | INL s =>
    if s = «~» then
      strip_rup_hint_aux xs (0::acc)
    else NONE)
End

Definition strip_rup_hint_def:
  strip_rup_hint xs = strip_rup_hint_aux xs []
End

Definition rup_hint_ok_def:
  (rup_hint_ok [] ⇔ T) ∧
  (rup_hint_ok (x::xs) ⇔
    (case x of INR n => n ≥ (0:int) | INL s => s = «~») ∧ rup_hint_ok xs)
End

(* The numbers of a checked token list; a non-number token stands for 0 *)
(* TMC *)
Definition tok_nums_def:
  (tok_nums [] = []) ∧
  (tok_nums (x::xs) =
    let y = (case x of INR n => Num n | INL _ => 0n) in
    y :: tok_nums xs)
End

Theorem strip_rup_hint_aux_ok:
  ∀xs acc.
  strip_rup_hint_aux xs acc =
  if rup_hint_ok xs then SOME (REVERSE acc ++ tok_nums xs) else NONE
Proof
  Induct
  >- rw[strip_rup_hint_aux_def,rup_hint_ok_def,tok_nums_def]>>
  Cases>>
  rw[strip_rup_hint_aux_def,rup_hint_ok_def,tok_nums_def]>>
  gvs[]
QED

Theorem strip_rup_hint_ok:
  strip_rup_hint xs =
  if rup_hint_ok xs then SOME (tok_nums xs) else NONE
Proof
  simp[strip_rup_hint_def,strip_rup_hint_aux_ok]
QED

Definition parse_rup_hint_def:
  (parse_rup_hint [] = NONE) ∧
  (parse_rup_hint (x::xs) =
    case x of
      INL s =>
      if s = «:» then strip_rup_hint xs else NONE
    | _ => NONE)
End

(* Parsing RUP step (header "rup", ";" stripped) *)
Definition parse_rup_def:
  parse_rup line =
  case parse_pbc_rest line of
    SOME (c,rest) =>
      (case parse_rup_hint rest of NONE => NONE
      | SOME ns => SOME (c,ns))
  | NONE => NONE
End

(*
  EVAL ``parse_rup (toks «1 ~x5 1 x26 +1 x27 1 x28 1 x29 >= 1 : 6 11 ~»)``
*)

Definition start_subproof_def:
  start_subproof rest ⇔
  rest = [INL «:»; INL «subproof»]
End

Definition colon_id_opt_def:
  colon_id_opt rest =
  case rest of
    [INL term; INR id] =>
    if term = «:» ∧ id ≥ 0 then SOME (SOME (Num id))
    else NONE
  | [] => SOME NONE
  | _ => NONE
End

Definition parse_pbc_header_def:
  parse_pbc_header line =
  case parse_pbc_rest line of
    SOME (c,rest) =>
      if start_subproof rest
      then SOME c
      else NONE
  | NONE => NONE
End

(*
  EVAL ``parse_pbc_header (toks «3 x1 -3 x2 2 x3 >= 5 : subproof»)``
*)

Definition strip_numbers_aux_def:
  (strip_numbers_aux [] acc = SOME (REVERSE acc)) ∧
  (strip_numbers_aux (x::xs) acc =
  case x of INR n =>
    if n ≥ 0 then
      strip_numbers_aux xs (Num n::acc)
    else NONE
  | INL _ => NONE)
End

Definition strip_numbers_def:
  strip_numbers xs = strip_numbers_aux xs []
End

Definition numbers_ok_def:
  (numbers_ok [] ⇔ T) ∧
  (numbers_ok (x::xs) ⇔
    (case x of INR n => n ≥ (0:int) | INL _ => F) ∧ numbers_ok xs)
End

Theorem strip_numbers_aux_ok:
  ∀xs acc.
  strip_numbers_aux xs acc =
  if numbers_ok xs then SOME (REVERSE acc ++ tok_nums xs) else NONE
Proof
  Induct
  >- rw[strip_numbers_aux_def,numbers_ok_def,tok_nums_def]>>
  Cases>>
  rw[strip_numbers_aux_def,numbers_ok_def,tok_nums_def]>>
  gvs[]
QED

Theorem strip_numbers_ok:
  strip_numbers xs =
  if numbers_ok xs then SOME (tok_nums xs) else NONE
Proof
  simp[strip_numbers_def,strip_numbers_aux_ok]
QED

(* qed mark : ID ; --- ID is optional *)
Definition check_mark_qed_id_opt_def:
  check_mark_qed_id_opt mark (h:(mlstring + int) list ) =
  case strip_term_line h of NONE => NONE
  | SOME rs =>
  case rs of
    INL q :: rest =>
    if q = «qed» then
      case rest of
        s :: rest' =>
        if s = mark
        then colon_id_opt rest'
        else colon_id_opt rest
      | [] => SOME NONE
    else NONE
  | _ => NONE
End

(* qed mark : ID ; *)
Definition check_mark_qed_id_def:
  check_mark_qed_id mark (h:(mlstring + int) list ) =
  case check_mark_qed_id_opt mark h of
    SOME (SOME res) => SOME res
  | _ => NONE
End

(*
EVAL `` check_mark_qed_id (INL «pbc») (toks «qed pbc : 4 ;»)``

EVAL `` check_mark_qed_id_opt (INL «pbc») (toks «qed pbc;»)``

EVAL `` check_mark_qed_id_opt (INL «pbc») (toks «qed;»)``
*)

Definition parse_var_def:
  parse_var v =
  case parse_lit v of
    SOME (Pos n) => SOME n
  | _ => NONE
End

(* Parse a substitution {var -> lit} *)
Definition parse_subst_aux_def:
  (parse_subst_aux (INL v :: INL arr :: r ::rest) acc =
  if arr = «->» then
    case parse_var v of
      NONE => ([],[])
    | SOME v =>
    (case r of
        INR r =>
          if r = 0:int then parse_subst_aux rest ((v,INL F)::acc)
          else if r = 1 then parse_subst_aux rest ((v,INL T)::acc)
          else ([],[])
      | INL r =>
          (case parse_lit r of NONE => ([],[])
          | SOME l => parse_subst_aux rest ((v,INR l)::acc)))
  else ([],[])) ∧
  (parse_subst_aux ls acc = (ls, acc:mlstring subst_raw))
End

Definition parse_subst_def:
  (parse_subst [] = NONE) ∧
  (parse_subst (x::xs) =
    case x of
      INL s =>
      if s = «:» then
      SOME (parse_subst_aux xs [])
      else NONE
    | _ => NONE)
End

(* A strengthening rule header *)
Definition parse_red_header_def:
  parse_red_header line =
  case parse_pbc_rest line of
    SOME (c,rest) =>
      (case parse_subst rest of
        NONE => NONE
      | SOME (rest,ss) =>
        if start_subproof rest
        then SOME (c,ss)
        else NONE)
  | NONE => NONE
End

(* parse a subproof and returns the next failing line
  Type subproof = ``:((((num + num) # num) option, (lstep list)) alist)``;
*)
Definition mk_acc_def:
  mk_acc pf acc = if pf = [] then acc else (NONE,pf)::acc
End

(* We map #n to n-1 internally *)
Definition parse_hash_num_def:
  parse_hash_num s =
  if strlen s ≥ 1 ∧ strsub_unsafe s 0 = #"#" then
    OPTION_MAP (λn. n-1)
      (mlint$fromNatString (substring s 1 (strlen s - 1)))
  else NONE
End

Definition parse_subgoal_num_def:
  parse_subgoal_num line =
  case line of
    [INR n] => if n>=0 then SOME (INL (Num n)) else NONE
  | [INL s] =>
    (case parse_hash_num s of
      SOME n => SOME (INR n)
    | NONE => NONE)
  | _ => NONE
End

Definition parse_proofgoal_def:
  parse_proofgoal (h:(mlstring + int) list ) =
  case h of
    INL e::rs =>
    (if e = «proofgoal» then
      parse_subgoal_num rs
    else NONE)
  | _ => NONE
End

Definition mk_proofgoal_mark_def:
  mk_proofgoal_mark (ind : num + num) =
  case ind of
    INL n => INR (&n:int)
  | INR n => INL («#» ^ toString (n+1))
End

(* leq -> 0, geq -> 1 *)
Definition parse_scopetext_def:
  parse_scopetext line =
  case line of
    [INL s] =>
    if s = «leq» then SOME 0
    else if s = «geq» then SOME 1
    else NONE
  | _ => NONE
End

Definition parse_scopehead_def:
  parse_scopehead (h:(mlstring + int) list ) =
  case h of
    INL e::rs =>
    (if e = «scope» then
      parse_scopetext rs
    else NONE)
  | _ => NONE
End

Definition mk_scope_mark_def:
  mk_scope_mark sc =
  if sc = 0n then [INL «scope»; INL «leq»]
  else [INL «scope»; INL «geq»]
End

Definition check_end_def:
  check_end marks (h:(mlstring + int) list ) =
  case strip_term_line h of NONE => F
  | SOME rs =>
  case rs of
    INL q :: rest =>
    q = «end» ∧
      (rest = [] ∨
      rest = marks)
  | _ => F
End

(* def_order parsing. We parse the sections in order.
  First, the vars block
*)
Definition parse_def_order_head_def:
  parse_preorder_head s =
  case s of
    [x;INL name] =>
      if x = INL «def_order» then
        SOME name
      else NONE
  | _ => NONE
End

Definition parse_vars_line_aux_def:
  (parse_vars_line_aux [] = SOME []) ∧
  (parse_vars_line_aux (x::xs) =
  case x of
    INL v =>
    (case parse_var v of
      NONE => NONE
    | SOME vv =>
      (case parse_vars_line_aux xs of NONE => NONE
      | SOME vvs => SOME (vv::vvs)))
  | _ => NONE)
End

Definition parse_vars_line_def:
  parse_vars_line n l =
  case strip_term_line l of
    SOME (h::rest) =>
    if h = INL n then
        parse_vars_line_aux rest
    else NONE
  | _ => NONE
End

Definition check_qed_def:
  check_qed marks (h:(mlstring + int) list ) =
  case strip_term_line h of NONE => F
  | SOME rs =>
  case rs of
    INL q :: rest =>
    q = «qed» ∧
      (rest = [] ∨
      rest = marks)
  | _ => F
End

Definition split_lit_def:
  split_lit l =
  case l of Pos v => (v,T) | Neg v => (v,F)
End

Definition parse_lits_line_aux_def:
  (parse_lits_line_aux [] = SOME []) ∧
  (parse_lits_line_aux (x::xs) =
  case x of
    INL v =>
    (case parse_lit v of
      NONE => NONE
    | SOME ll =>
      (case parse_lits_line_aux xs of NONE => NONE
      | SOME lls => SOME (split_lit ll::lls)))
  | _ => NONE)
End

Definition parse_assg_def:
  (parse_assg [] acc = SOME (acc,NONE)) ∧
  (parse_assg (INL s::ss) acc =
    case parse_lit s of
      NONE =>
        if s = «:» then
          (case ss of [INR i] => SOME (acc,SOME i)
          | _ => NONE)
        else NONE
    | SOME l => parse_assg ss (split_lit l :: acc)) ∧
  (parse_assg _ acc = NONE)
End

Definition parse_solx_aux_def:
  (parse_solx_aux [] assg free = SOME (assg,free)) ∧
  (parse_solx_aux (INL s::ss) assg free =
    if strlen s > 0 ∧ strsub_unsafe s 0 = #"*" then
      case parse_var (substring s 1 (strlen s - 1)) of
        NONE => NONE
      | SOME v => parse_solx_aux ss assg (v::free)
    else
      case parse_lit s of
        NONE => NONE
      | SOME l => parse_solx_aux ss (split_lit l::assg) free) ∧
  (parse_solx_aux _ assg free = NONE)
End

Definition parse_delc_header_def:
  parse_delc_header line =
  case line of
    INR id::rest =>
    if id ≥ 0 then
      (case parse_subst rest of
        NONE => NONE
      | SOME (rest,ss) =>
        if start_subproof rest
        then SOME (Num id,ss)
        else NONE)
    else NONE
  | _ => NONE
End

(*
EVAL``parse_delc_header (toks «2 : x1 -> ~x2 : subproof»)``
*)

(* Take off : subproof at the end *)
Definition strip_obju_end_def:
  strip_obju_end ls =
  let lls = LENGTH ls in
  if lls < 2
  then
    NONE
  else
    let tls = TAKE (lls-2) ls in
    let dls = DROP (lls-2) ls in
    if start_subproof dls
    then SOME tls
    else NONE
End

Definition parse_b_obj_term_def:
  (parse_b_obj_term rest =
   case strip_obju_end rest of NONE => NONE
  | SOME [] => NONE
  | SOME (r::rs) =>
  case parse_obj_term rs of NONE => NONE
  | SOME f =>
    if r = INL «new» then SOME (T,f)
    else if r = INL «diff» then SOME (F,f)
    else NONE)
End

(*
EVAL``parse_b_obj_term (toks «new 1 x1 2 : subproof»)``
*)

(* preserve_add and remove steps *)
Definition parse_preserve_def:
  (parse_preserve rest =
   case strip_obju_end rest of
   | SOME (INL c::INL s::cs) =>
    if s = «:» then
      (case parse_var c of
        NONE => NONE
      | SOME x =>
      (case parse_pbc_rest cs of
        SOME (constr,[]) => SOME (x,constr)
        | _ => NONE))
    else NONE
  | _ => NONE)
End

(*
  EVAL``parse_preserve (toks «x1 : 1 x1 2 x2 >= 5 : subproof»)``
*)

(* A proof line, its names not yet numbered *)
Datatype:
  pline =
  | PbcHd ('a pbc)                                (* pbc ... : subproof *)
  | Pol ('a constr)
  | RupL ('a pbc) (num list)
  | CheckL num ('a pbc)                           (* e *)
  | ImplyL num ('a pbc)                           (* ia *)
  | RedHd ('a pbc) ('a subst_raw)                 (* red ... : subproof *)
  | DomHd ('a pbc) ('a subst_raw)                 (* dom ... : subproof *)
  | DelcHd num ('a subst_raw)                     (* delc ... : subproof *)
  | ObjuHd bool ((int # 'a lit) list # int)       (* obju ... : subproof *)
  | PresHd bool 'a ('a pbc)                       (* preserved_* ... : subproof *)
  | LoadOrd mlstring (('a # bool) list)
  | SolL ('a assg_raw) bool (int option)          (* sol, soli *)
  | SolxL ('a assg_raw) ('a list)
  | EObj ((int # 'a lit) list # int)
  | EPres ('a list)
  | OrdHd mlstring                                (* def_order *)
  | LDone lstep                                   (* steps without names *)
  | CDone cstep
End

(*
  The keywords of the three kinds of lines (lsteps, the red header and the
  csteps) are disjoint, so one dispatch reads all of them. The lines that
  structure a proof (qed, proofgoal, scope, end, output, conclusion) are
  not plines: parse_line returns NONE for them, as for a line that does
  not parse.
*)
Definition parse_line_def:
  parse_line s =
  case s of
    [] => NONE
  | INR _ :: rs => NONE
  | INL k :: rs =>
    if k = «pol» then
      (case strip_term_line rs of NONE => NONE
      | SOME rs =>
        case parse_cutting rs of NONE => NONE
        | SOME c => SOME (Pol c))
    else if k = «rup» then
      (case strip_term_line rs of NONE => NONE
      | SOME rs =>
        case parse_rup rs of NONE => NONE
        | SOME (c,ns) => SOME (RupL c ns))
    else if k = «pbc» then
      (case parse_pbc_header rs of NONE => NONE
      | SOME c => SOME (PbcHd c))
    else if k = «red» then
      (case parse_red_header rs of NONE => NONE
      | SOME (c,ss) => SOME (RedHd c ss))
    else if k = «dom» then
      (case parse_red_header rs of NONE => NONE
      | SOME (c,ss) => SOME (DomHd c ss))
    else if k = «delc» then
      (case parse_delc_header rs of
        SOME (n,ss) => SOME (DelcHd n ss)
      | NONE =>
        case strip_term_line rs of NONE => NONE
        | SOME rs =>
          case strip_numbers rs of NONE => NONE
          | SOME n => SOME (CDone (UncheckedDelete n)))
    else if k = «def_order» then
      (case rs of [INL n] => SOME (OrdHd n)
      | _ => NONE)
    else if k = «obju» then
      (case parse_b_obj_term rs of NONE => NONE
      | SOME (b,f) => SOME (ObjuHd b f))
    else if k = «preserved_add» then
      (case parse_preserve rs of NONE => NONE
      | SOME (x,c) => SOME (PresHd T x c))
    else if k = «preserved_rm» then
      (case parse_preserve rs of NONE => NONE
      | SOME (x,c) => SOME (PresHd F x c))
    else
    case strip_term_line rs of NONE => NONE
    | SOME rs =>
    if k = «deld» then
      (case strip_numbers rs of NONE => NONE
      | SOME n => SOME (LDone (Delete n)))
    else if k = «e» then
      (case parse_pbc_rest rs of NONE => NONE
      | SOME (c,rest) =>
        case colon_id_opt rest of
          SOME (SOME id) => SOME (CheckL id c)
        | _ => NONE)
    else if k = «ia» then
      (case parse_pbc_rest rs of NONE => NONE
      | SOME (c,rest) =>
        case colon_id_opt rest of
          SOME (SOME id) => SOME (ImplyL id c)
        | _ => NONE)
    else if k = «*» then SOME (LDone NoOp)
    else if k = «core» then
      (case rs of
        INL r :: ns =>
          if r = «id» then
            (case strip_numbers ns of NONE => NONE
            | SOME n => SOME (CDone (Transfer n)))
          else NONE
      | _ => NONE)
    else if k = «strengthening_to_core» then
      (case rs of
        [INL b] =>
          if b = «on» then SOME (CDone (StrengthenToCore T))
          else if b = «off» then SOME (CDone (StrengthenToCore F))
          else NONE
      | _ => NONE)
    else if k = «load_order» then
      (case rs of
        [] => SOME (CDone UnloadOrder)
      | INL r :: ws =>
        (case parse_lits_line_aux ws of NONE => NONE
        | SOME ws => SOME (LoadOrd r ws))
      | _ => NONE)
    else if k = «soli» then
      (case parse_assg rs [] of NONE => NONE
      | SOME (assg,ov) => SOME (SolL assg T ov))
    else if k = «sol» then
      (case parse_assg rs [] of NONE => NONE
      | SOME (assg,ov) => SOME (SolL assg F ov))
    else if k = «solx» then
      (case parse_solx_aux rs [] [] of NONE => NONE
      | SOME (assg,free) => SOME (SolxL assg free))
    else if k = «obji» then
      (case rs of [INR i] => SOME (CDone (AssertObj i))
      | _ => NONE)
    else if k = «eobj» then
      (case parse_obj_term rs of NONE => NONE
      | SOME f => SOME (EObj f))
    else if k = «epreserved» then
      (case parse_vars_line_aux rs of NONE => NONE
      | SOME vs => SOME (EPres vs))
    else NONE
End

(*
  EVAL ``parse_line (toks «dom 1 ~x1 1 x2 >= 1 : x1 -> x2 x2 -> x1 : subproof»)``;
  EVAL ``parse_line (toks «delc 2 : : subproof»)``;
  EVAL ``parse_line (toks «delc 1 2 3 4 5;»)``;
  EVAL ``parse_line (toks «load_order lex10 x1 ~x4 x9 ~x10 ;»)``;
  EVAL ``parse_line (toks «strengthening_to_core off;»)``;
  EVAL ``parse_line (toks «core id 1 2 3 4 5;»)``;
  EVAL ``parse_line (toks «soli ~x1 ~x2 ~x3 x7 ~x8 : 50;»)``;
  EVAL ``parse_line (toks «solx ~x1 *x2 ~x3 ;»)``;
  EVAL ``parse_line (toks «obji -100 ;»)``;
  EVAL ``parse_line (toks «eobj 1 x1 -100 ;»)``;
  EVAL ``parse_line (toks «epreserved x3 x2 x5;»)``;
  EVAL ``parse_line (toks «obju new 1 x1 2 : subproof»)``;
  EVAL ``parse_line (toks «red 1 x1 >= 1 : x1 -> x3 x3 -> x5 : subproof»)``;
  EVAL ``parse_line (toks «pbc +3 x1 +3 x2 +2 x3 >= 5 : subproof»)``;
  EVAL ``parse_line (toks «rup >= 1 : 1234;»)``;
*)

(* parse a hconcl *)
Definition parse_unsat_def:
  parse_unsat rest =
  case rest of
    [INL s; INR n] =>
    if s = «:» ∧ n ≥ 0 then SOME (Num n) else NONE
  | _ => NONE
End

Definition parse_sat_def:
  parse_sat rest =
  case rest of
    INL s::rest =>
    if s = «:» then
      (case parse_assg rest [] of NONE => NONE
      | SOME (a,_) => SOME (SOME a))
    else NONE
  | [] => SOME NONE
  | _ => NONE
End

(* Parse a number or infinity *)
Definition parse_int_inf_def:
  parse_int_inf l =
  case l of INR n => SOME (SOME n)
  | INL s => if s = «INF» then SOME NONE else NONE
End

(* lb : id ub [: optional assignment] *)
Definition parse_lb_def:
  parse_lb s =
  case s of
    lb :: INL s :: INR n :: rest =>
    if s = «:» ∧ n ≥ 0 then
      case parse_int_inf lb of NONE => NONE
      | SOME lb => SOME ((lb,Num n), rest)
    else NONE
  | _ => NONE
End

Definition parse_ub_def:
  parse_ub s =
  case s of
    ub :: rest =>
      (case parse_int_inf ub of NONE => NONE
      | SOME ub =>
        (case rest of [] => SOME(ub, NONE)
        | INL s::rest =>
          if s = «:» then
            (case parse_assg rest [] of NONE => NONE
            | SOME (a,_) => SOME(ub,SOME a))
          else NONE
        | _ => NONE))
    | _ => NONE
End

(* parse hints for OBound *)
Definition parse_bounds_def:
  parse_bounds rest =
  case parse_lb rest of NONE => NONE
  | SOME ((lb,n),rest') =>
    (case parse_ub rest' of NONE => NONE
    | SOME (ub,a) => SOME (lb,ub,n,a))
End

Definition parse_enum_def:
  parse_enum s =
  case s of
    INR n :: rest =>
      if n < 0 then NONE
      else
        (case rest of [] => SOME(Num n, NONE)
        | INL s::INR i :: rest =>
          if s = «:» ∧ i ≥ 0 then
              SOME (Num n, SOME (Num i))
          else NONE
        | _ => NONE)
    | _ => NONE
End

Definition parse_concl_def:
  parse_concl s =
  case strip_term_line s of NONE => NONE
  | SOME s =>
  case s of
  x::y::rest =>
  if x = INL «conclusion» then
    if y = INL «NONE» ∧ rest = [] then SOME (HNoConcl:mlstring hconcl)
    else if y = INL «UNSAT» then
      OPTION_MAP HDUnsat (parse_unsat rest)
    else if y = INL «SAT» then
      OPTION_MAP HDSat (parse_sat rest)
    else if y = INL «BOUNDS» then
      case parse_bounds rest of NONE => NONE
      | SOME (lb,ub,n,a) => SOME (HOBounds lb ub n a)
    else if y = INL «ENUMERATION_COMPLETE» then
      (case parse_enum rest of NONE => NONE
      | SOME (n, hint) => SOME (HEEnum n T hint))
    else if y = INL «ENUMERATION_PARTIAL» then
      (case parse_enum rest of NONE => NONE
      | SOME (n, hint) => SOME (HEEnum n F hint))
    else NONE
  else NONE
  | _ => NONE
End

(*
  EVAL ``parse_concl (toks «conclusion NONE ;»)``;
  EVAL ``parse_concl (toks «conclusion UNSAT : 1234 ;»)``;
  EVAL ``parse_concl (toks «conclusion SAT : x1 ~x2 ;»)``;
  EVAL ``parse_concl (toks «conclusion ENUMERATION_PARTIAL 5 ;»)``;
*)

(* Parse a PBC output line.
  TODO: equienumerable currently aliases equisolvable *)
Definition parse_output_def:
  parse_output s =
  case strip_term_line s of NONE => NONE
  | SOME s =>
  case s of
    [x;y] =>
    if x = INL «output» ∧ y = INL «NONE»
    then SOME NoOutput
    else NONE
  | [x;y;z] =>
    if x = INL «output» ∧ z = INL «FILE»
    then (
      if y = INL «DERIVABLE» then SOME Derivable
      else if y = INL «EQUISATISFIABLE» then SOME Equisatisfiable
      else if y = INL «EQUIOPTIMAL» then SOME Equioptimal
      else if y = INL «EQUIENUMERABLE» then SOME Equisolvable
      else if y = INL «EQUISOLVABLE» then SOME Equisolvable
      else NONE)
    else NONE
  | _ => NONE
End

(*
  Numbering the names of a line, left to right (name_table)
*)
Definition name_subst_def:
  (name_subst lim [] s = SOME ([],s)) ∧
  (name_subst lim ((v,r)::ss) s =
    case res_var lim v s of
      NONE => NONE
    | SOME (n,s1) =>
      case r of
        INL b =>
        (case name_subst lim ss s1 of
          NONE => NONE
        | SOME (ss1,s2) => SOME ((n,INL b)::ss1,s2))
      | INR l =>
        (case name_lit lim l s1 of
          NONE => NONE
        | SOME (l1,s2) =>
          case name_subst lim ss s2 of
            NONE => NONE
          | SOME (ss1,s3) => SOME ((n,INR l1)::ss1,s3)))
End

(* Triv and Lincomb are formed by the checker and never parsed *)
Definition name_constr_def:
  (name_constr lim (Id n) s = SOME (Id n,s)) ∧
  (name_constr lim (Add c1 c2) s =
    case name_constr lim c1 s of
      NONE => NONE
    | SOME (d1,s1) =>
      case name_constr lim c2 s1 of
        NONE => NONE
      | SOME (d2,s2) => SOME (Add d1 d2,s2)) ∧
  (name_constr lim (Mul c k) s =
    case name_constr lim c s of
      NONE => NONE
    | SOME (d,s1) => SOME (Mul d k,s1)) ∧
  (name_constr lim (Div dt c k) s =
    case name_constr lim c s of
      NONE => NONE
    | SOME (d,s1) => SOME (Div dt d k,s1)) ∧
  (name_constr lim (Minus c k) s =
    case name_constr lim c s of
      NONE => NONE
    | SOME (d,s1) => SOME (Minus d k,s1)) ∧
  (name_constr lim (Sat c) s =
    case name_constr lim c s of
      NONE => NONE
    | SOME (d,s1) => SOME (Sat d,s1)) ∧
  (name_constr lim (Lit l) s =
    case name_lit lim l s of
      NONE => NONE
    | SOME (l1,s1) => SOME (Lit l1,s1)) ∧
  (name_constr lim (Weak c vs) s =
    case name_constr lim c s of
      NONE => NONE
    | SOME (d,s1) =>
      case name_vars lim vs s1 of
        NONE => NONE
      | SOME (ns,s2) => SOME (Weak d ns,s2)) ∧
  (name_constr lim (Triv _) s = NONE) ∧
  (name_constr lim (Lincomb _ _) s = NONE)
End

Definition name_hconcl_def:
  (name_hconcl lim HNoConcl s = SOME (HNoConcl,s)) ∧
  (name_hconcl lim (HDSat NONE) s = SOME (HDSat NONE,s)) ∧
  (name_hconcl lim (HDSat (SOME a)) s =
    case name_assg lim a s of
      NONE => NONE
    | SOME (a1,s1) => SOME (HDSat (SOME a1),s1)) ∧
  (name_hconcl lim (HDUnsat n) s = SOME (HDUnsat n,s)) ∧
  (name_hconcl lim (HOBounds lb ub n NONE) s = SOME (HOBounds lb ub n NONE,s)) ∧
  (name_hconcl lim (HOBounds lb ub n (SOME a)) s =
    case name_assg lim a s of
      NONE => NONE
    | SOME (a1,s1) => SOME (HOBounds lb ub n (SOME a1),s1)) ∧
  (name_hconcl lim (HEEnum n b h) s = SOME (HEEnum n b h,s))
End

Definition name_pline_def:
  (name_pline lim (PbcHd c) s =
    case name_pbc lim c s of
      NONE => NONE
    | SOME (c1,s1) => SOME (PbcHd c1,s1)) ∧
  (name_pline lim (Pol c) s =
    case name_constr lim c s of
      NONE => NONE
    | SOME (c1,s1) => SOME (Pol c1,s1)) ∧
  (name_pline lim (RupL c ns) s =
    case name_pbc lim c s of
      NONE => NONE
    | SOME (c1,s1) => SOME (RupL c1 ns,s1)) ∧
  (name_pline lim (CheckL n c) s =
    case name_pbc lim c s of
      NONE => NONE
    | SOME (c1,s1) => SOME (CheckL n c1,s1)) ∧
  (name_pline lim (ImplyL n c) s =
    case name_pbc lim c s of
      NONE => NONE
    | SOME (c1,s1) => SOME (ImplyL n c1,s1)) ∧
  (name_pline lim (RedHd c ss) s =
    case name_pbc lim c s of
      NONE => NONE
    | SOME (c1,s1) =>
      case name_subst lim ss s1 of
        NONE => NONE
      | SOME (ss1,s2) => SOME (RedHd c1 ss1,s2)) ∧
  (name_pline lim (DomHd c ss) s =
    case name_pbc lim c s of
      NONE => NONE
    | SOME (c1,s1) =>
      case name_subst lim ss s1 of
        NONE => NONE
      | SOME (ss1,s2) => SOME (DomHd c1 ss1,s2)) ∧
  (name_pline lim (DelcHd n ss) s =
    case name_subst lim ss s of
      NONE => NONE
    | SOME (ss1,s1) => SOME (DelcHd n ss1,s1)) ∧
  (name_pline lim (ObjuHd b (f,k)) s =
    case name_lin lim f s of
      NONE => NONE
    | SOME (f1,s1) => SOME (ObjuHd b (f1,k),s1)) ∧
  (name_pline lim (PresHd b x c) s =
    case res_var lim x s of
      NONE => NONE
    | SOME (n,s1) =>
      case name_pbc lim c s1 of
        NONE => NONE
      | SOME (c1,s2) => SOME (PresHd b n c1,s2)) ∧
  (name_pline lim (LoadOrd r ws) s =
    case name_assg lim ws s of
      NONE => NONE
    | SOME (ws1,s1) => SOME (LoadOrd r ws1,s1)) ∧
  (name_pline lim (SolL a b ov) s =
    case name_assg lim a s of
      NONE => NONE
    | SOME (a1,s1) => SOME (SolL a1 b ov,s1)) ∧
  (name_pline lim (SolxL a fr) s =
    case name_assg lim a s of
      NONE => NONE
    | SOME (a1,s1) =>
      case name_vars lim fr s1 of
        NONE => NONE
      | SOME (fr1,s2) => SOME (SolxL a1 fr1,s2)) ∧
  (name_pline lim (EObj (f,k)) s =
    case name_lin lim f s of
      NONE => NONE
    | SOME (f1,s1) => SOME (EObj (f1,k),s1)) ∧
  (name_pline lim (EPres vs) s =
    case name_vars lim vs s of
      NONE => NONE
    | SOME (ns,s1) => SOME (EPres ns,s1)) ∧
  (name_pline lim (OrdHd n) s = SOME (OrdHd n,s)) ∧
  (name_pline lim (LDone st) s = SOME (LDone st,s)) ∧
  (name_pline lim (CDone st) s = SOME (CDone st,s))
End

(*
  Finishing a numbered line
*)

(* A proof-file constraint is accepted exactly when its head expands to a
  single normalised constraint, since lstep/sstep hold one npbc *)
Definition mk_npbc_def:
  mk_npbc (c:num pbc) =
  case to_gnpbc c of
    [gc] => SOME (inject gc)
  | _ => NONE
End

Definition is_lstep_def:
  (is_lstep (PbcHd _) ⇔ T) ∧
  (is_lstep (Pol _) ⇔ T) ∧
  (is_lstep (RupL _ _) ⇔ T) ∧
  (is_lstep (CheckL _ _) ⇔ T) ∧
  (is_lstep (ImplyL _ _) ⇔ T) ∧
  (is_lstep (LDone _) ⇔ T) ∧
  (is_lstep _ ⇔ F)
End

(* The lstep of a one-line lstep *)
Definition fin_lstep_def:
  (fin_lstep (Pol c) = SOME (Cutting c)) ∧
  (fin_lstep (RupL c ns) =
    case mk_npbc c of
      NONE => NONE
    | SOME c1 => SOME (Rup c1 ns)) ∧
  (fin_lstep (CheckL n c) =
    case mk_npbc c of
      NONE => NONE
    | SOME c1 => SOME (Check n c1)) ∧
  (fin_lstep (ImplyL n c) =
    case mk_npbc c of
      NONE => NONE
    | SOME c1 => SOME (ImplyAdd n c1)) ∧
  (fin_lstep (LDone st) = SOME st) ∧
  (fin_lstep _ = NONE)
End

(* The cstep of a one-line cstep *)
Definition fin_cstep_def:
  (fin_cstep (CDone st) = SOME st) ∧
  (fin_cstep (LoadOrd r ws) = SOME (LoadOrder r ws)) ∧
  (fin_cstep (SolL a b ov) = SOME (Obj a b ov)) ∧
  (fin_cstep (SolxL a fr) = SOME (Sol a (list_to_num_set fr))) ∧
  (fin_cstep (EObj f) =
    case normalise_obj (SOME f) of
      NONE => NONE
    | SOME f1 => SOME (CheckObj f1)) ∧
  (fin_cstep (EPres vs) = SOME (CheckPres (list_to_num_set vs))) ∧
  (fin_cstep _ = NONE)
End

(*
  The proof readers of npbc_parseProg, over a list of tokenized lines.
  lim and s are the table's limit and numbering state; each reader returns
  the state after the lines it read.
*)

(* Parsing lsteps in a subproof until a line that is not an lstep, which
  is returned with the remaining lines *)
Definition parse_lsteps_aux_def:
  (parse_lsteps_aux lim s ([]:(mlstring + int) list list) (acc:lstep list) =
    NONE) ∧
  (parse_lsteps_aux lim s (l::ls) acc =
    case parse_line l of
      NONE => SOME (REVERSE acc,s,l,ls)
    | SOME pl =>
      if is_lstep pl then
        case name_pline lim pl s of
          NONE => NONE
        | SOME (pl1,s1) =>
          case pl1 of
            PbcHd c =>
            (case mk_npbc c of
              NONE => NONE
            | SOME c1 =>
              case parse_lsteps_aux lim s1 ls [] of
                NONE => NONE
              | SOME (pf,s2,l2,rest) =>
                if LENGTH rest < LENGTH ls then
                  case check_mark_qed_id (INL «pbc») l2 of
                    NONE => NONE
                  | SOME id => parse_lsteps_aux lim s2 rest (Con c1 pf id::acc)
                else NONE)
          | _ =>
            (case fin_lstep pl1 of
              NONE => NONE
            | SOME step => parse_lsteps_aux lim s1 ls (step::acc))
      else SOME (REVERSE acc,s,l,ls))
Termination
  WF_REL_TAC ‘measure (LENGTH o FST o SND o SND)’
  \\ rw[] \\ fs[]
End

Theorem parse_lsteps_aux_LENGTH:
  ∀lim s ss acc acc' s' l ss'.
  parse_lsteps_aux lim s ss acc = SOME(acc',s',l,ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  ho_match_mp_tac parse_lsteps_aux_ind>>
  rpt strip_tac>>
  qpat_x_assum`parse_lsteps_aux _ _ _ _ = _` mp_tac>>
  simp[Once parse_lsteps_aux_def]>>
  rw[AllCaseEqs()]>>
  gvs[]
QED

Theorem parse_lsteps_aux_thm:
  (∀lim s acc.
    parse_lsteps_aux lim s ([]:(mlstring + int) list list) acc = NONE) ∧
  (∀lim s l ls acc.
    parse_lsteps_aux lim s (l::ls) acc =
    case parse_line l of
      NONE => SOME (REVERSE acc,s,l,ls)
    | SOME pl =>
      if is_lstep pl then
        case name_pline lim pl s of
          NONE => NONE
        | SOME (pl1,s1) =>
          case pl1 of
            PbcHd c =>
            (case mk_npbc c of
              NONE => NONE
            | SOME c1 =>
              case parse_lsteps_aux lim s1 ls [] of
                NONE => NONE
              | SOME (pf,s2,l2,rest) =>
                case check_mark_qed_id (INL «pbc») l2 of
                  NONE => NONE
                | SOME id => parse_lsteps_aux lim s2 rest (Con c1 pf id::acc))
          | _ =>
            (case fin_lstep pl1 of
              NONE => NONE
            | SOME step => parse_lsteps_aux lim s1 ls (step::acc))
      else SOME (REVERSE acc,s,l,ls))
Proof
  rw[]
  >- simp[Once parse_lsteps_aux_def]>>
  simp[Once parse_lsteps_aux_def]>>
  rpt (TOP_CASE_TAC>>gvs[])>>
  imp_res_tac parse_lsteps_aux_LENGTH
QED

Definition parse_lsteps_def:
  parse_lsteps lim s ss = parse_lsteps_aux lim s ss []
End

(* Parsing a subproof: lsteps and proofgoals, up to the first line that is
  neither *)
Definition parse_subproof_aux_def:
  parse_subproof_aux lim s ss (acc:subproof) =
  case parse_lsteps lim s ss of
    NONE => NONE
  | SOME (pf,s1,l,rest) =>
    let acc = mk_acc pf acc in
    case parse_proofgoal l of
      NONE => SOME (REVERSE acc,s1,l,rest)
    | SOME ind =>
      (case parse_lsteps lim s1 rest of
        NONE => NONE
      | SOME (pf,s2,l2,rest2) =>
        case check_mark_qed_id (mk_proofgoal_mark ind) l2 of
          NONE => NONE
        | SOME id =>
          parse_subproof_aux lim s2 rest2 ((SOME (ind,id),pf)::acc))
Termination
  WF_REL_TAC ‘measure (LENGTH o FST o SND o SND)’
  \\ rw[] \\ fs[parse_lsteps_def]>>
  imp_res_tac parse_lsteps_aux_LENGTH>>
  fs[]
End

Definition parse_subproof_def:
  parse_subproof lim s ss = parse_subproof_aux lim s ss []
End

Theorem parse_subproof_aux_LENGTH:
  ∀lim s ss acc res s' l ss'.
  parse_subproof_aux lim s ss acc = SOME(res,s',l,ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  ho_match_mp_tac parse_subproof_aux_ind>>
  rpt strip_tac>>
  qpat_x_assum`parse_subproof_aux _ _ _ _ = _` mp_tac>>
  simp[Once parse_subproof_aux_def,parse_lsteps_def]>>
  rw[AllCaseEqs()]>>
  imp_res_tac parse_lsteps_aux_LENGTH>>
  gvs[parse_lsteps_def]
QED

(* Parsing a scope: subproofs and scope blocks, up to the first line that
  is neither *)
Definition parse_scope_aux_def:
  parse_scope_aux lim s ss (acc:(num option, subproof) alist) =
  case parse_subproof lim s ss of
    NONE => NONE
  | SOME (pf,s1,l,rest) =>
    let acc = mk_acc pf acc in
    case parse_scopehead l of
      NONE => SOME (REVERSE acc,s1,l,rest)
    | SOME ind =>
      (case parse_subproof lim s1 rest of
        NONE => NONE
      | SOME (pf,s2,l2,rest2) =>
        if check_end (mk_scope_mark ind) l2
        then parse_scope_aux lim s2 rest2 ((SOME ind,pf)::acc)
        else NONE)
Termination
  WF_REL_TAC ‘measure (LENGTH o FST o SND o SND)’
  \\ rw[parse_subproof_def]>>
  imp_res_tac parse_subproof_aux_LENGTH>>
  fs[]
End

Definition parse_scope_def:
  parse_scope lim s ss = parse_scope_aux lim s ss []
End

Theorem parse_scope_aux_LENGTH:
  ∀lim s ss acc res s' l ss'.
  parse_scope_aux lim s ss acc = SOME(res,s',l,ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  ho_match_mp_tac parse_scope_aux_ind>>
  rpt strip_tac>>
  qpat_x_assum`parse_scope_aux _ _ _ _ = _` mp_tac>>
  simp[Once parse_scope_aux_def,parse_subproof_def]>>
  rw[AllCaseEqs()]>>
  imp_res_tac parse_subproof_aux_LENGTH>>
  gvs[parse_subproof_def]
QED

(*
  The order block, after its def_order line
*)
Definition parse_vars_block_def:
  parse_vars_block lim s ss =
  case ss of
    v::l::r::ae::rest =>
    if v = [INL «vars»] then
      case parse_vars_line «left» l of NONE => NONE
      | SOME us =>
      case name_vars lim us s of NONE => NONE
      | SOME (us1,s1) =>
      case parse_vars_line «right» r of NONE => NONE
      | SOME vs =>
      case name_vars lim vs s1 of NONE => NONE
      | SOME (vs1,s2) =>
      if check_end [INL «vars»] ae then SOME ((us1,vs1,[]),s2,rest)
      else
        case parse_vars_line «aux» ae of NONE => NONE
        | SOME as =>
        case name_vars lim as s2 of NONE => NONE
        | SOME (as1,s3) =>
        case rest of
          e::rest1 =>
          if check_end [INL «vars»] e then SOME ((us1,vs1,as1),s3,rest1)
          else NONE
        | [] => NONE
    else NONE
  | _ => NONE
End

(* The red steps of a spec block, up to its end line *)
Definition parse_spec_aux_def:
  (parse_spec_aux lim s [] acc = NONE) ∧
  (parse_spec_aux lim s (l::ls) acc =
    case parse_line l of
      SOME (RedHd c ss) =>
      (case name_pbc lim c s of NONE => NONE
      | SOME (c1,s1) =>
        case name_subst lim ss s1 of NONE => NONE
        | SOME (ss1,s2) =>
          case mk_npbc c1 of NONE => NONE
          | SOME c2 =>
            case parse_scope lim s2 ls of NONE => NONE
            | SOME (pf,s3,l3,rest) =>
              if LENGTH rest < LENGTH ls then
                case check_mark_qed_id_opt (INL «red») l3 of NONE => NONE
                | SOME idopt =>
                  parse_spec_aux lim s3 rest ((c2,ss1,pf,idopt)::acc)
              else NONE)
    | _ =>
      if check_end [INL «spec»] l then SOME (REVERSE acc,s,ls)
      else NONE)
Termination
  WF_REL_TAC ‘measure (LENGTH o FST o SND o SND)’
  \\ rw[]
End

(* The optional spec block and the def line after it *)
Definition parse_spec_block_def:
  parse_spec_block lim s ss =
  case ss of
    h::rest =>
    if h = [INL «spec»] then
      case parse_spec_aux lim s rest [] of NONE => NONE
      | SOME (spec,s1,rest1) =>
        case rest1 of
          h1::rest2 =>
          if h1 = [INL «def»] then SOME (spec,s1,rest2) else NONE
        | [] => NONE
    else if h = [INL «def»] then SOME ([],s,rest)
    else NONE
  | [] => NONE
End

(* The constraints of a def block, up to its end line *)
Definition parse_def_aux_def:
  (parse_def_aux lim s [] acc = NONE) ∧
  (parse_def_aux lim s (l::ls) acc =
    if check_end [INL «def»] l then SOME (REVERSE acc,s,ls)
    else
      case parse_constraint_ns l of NONE => NONE
      | SOME c =>
        case name_pbc lim c s of NONE => NONE
        | SOME (c1,s1) =>
          case mk_npbc c1 of NONE => NONE
          | SOME c2 => parse_def_aux lim s1 ls (c2::acc))
End

(* The first two lines of a transitivity block *)
Definition trans_vars_head_def:
  trans_vars_head h v ⇔ h = [INL «transitivity»] ∧ v = [INL «vars»]
End

Definition parse_trans_vars_def:
  parse_trans_vars lim s ss =
  case ss of
    h::v::f::ae::rest =>
    if trans_vars_head h v then
      case parse_vars_line «fresh_right» f of NONE => NONE
      | SOME ws =>
      case name_vars lim ws s of NONE => NONE
      | SOME (ws1,s1) =>
      if check_end [INL «vars»] ae then SOME ((ws1,[],[]),s1,rest)
      else
        case parse_vars_line «fresh_aux_1» ae of NONE => NONE
        | SOME bs =>
        case name_vars lim bs s1 of NONE => NONE
        | SOME (bs1,s2) =>
        case rest of
          a2::e::rest1 =>
          (case parse_vars_line «fresh_aux_2» a2 of NONE => NONE
          | SOME cs =>
          case name_vars lim cs s2 of NONE => NONE
          | SOME (cs1,s3) =>
          if check_end [INL «vars»] e then SOME ((ws1,bs1,cs1),s3,rest1)
          else NONE)
        | _ => NONE
    else NONE
  | _ => NONE
End

(* A proof block without scopes, with a "proof" line, a "qed" line and an
  "end" line *)
Definition parse_proof_block_def:
  parse_proof_block lim s end ss =
  case ss of [] => NONE
  | h::ss =>
  if h = [INL «proof»] then
    case parse_subproof lim s ss of
    | SOME (pf,s1,l,rest) =>
      if check_qed [INL «proof»] l
      then
        case rest of [] => NONE
        | (e::rest1) =>
          if check_end end e
          then SOME (pf,s1,rest1)
          else NONE
      else NONE
    | _ => NONE
  else NONE
End

Definition parse_trans_block_def:
  parse_trans_block lim s ss =
  case parse_trans_vars lim s ss of
    NONE => NONE
  | SOME ((ws,bs,cs),s1,rest) =>
  case parse_proof_block lim s1 [INL «transitivity»] rest of
    NONE => NONE
  | SOME (pf,s2,rest1) => SOME ((ws,bs,cs,pf),s2,rest1)
End

Definition parse_refl_block_def:
  parse_refl_block lim s ss =
  case ss of
    h::ss =>
    if h = [INL «reflexivity»] then
      parse_proof_block lim s [INL «reflexivity»] ss
    else NONE
  | _ => NONE
End

Definition parse_pre_order_def:
  parse_pre_order lim s ss =
  case parse_vars_block lim s ss of NONE => NONE
  | SOME (vars,s1,ss1) =>
  case parse_spec_block lim s1 ss1 of NONE => NONE
  | SOME (gspec,s2,ss2) =>
  case parse_def_aux lim s2 ss2 [] of NONE => NONE
  | SOME (f,s3,ss3) =>
  case parse_trans_block lim s3 ss3 of NONE => NONE
  | SOME (pft,s4,ss4) =>
  case parse_refl_block lim s4 ss4 of NONE => NONE
  | SOME (pfr,s5,ss5) =>
  case ss5 of
    h::rest =>
    if check_end [INL «def_order»] h then
      SOME (vars,gspec,f,pfr,pft,s5,rest)
    else NONE
  | [] => NONE
End

(*
  EVAL``parse_pre_order NONE (nt_init 0)
  (MAP toks ([
  «vars»;
  «left u1;»;
  «right v1;»;
  «aux $a1;»;
  «end;»;
  «spec»;
  «red 1 u1 1 ~v1 1 ~$a1 >= 1 : $a1 -> 0 : subproof»;
  «qed;»;
  «end;»;
  «def»;
  «1 $d10 >= 1;»;
  «end;»;
  «transitivity»;
  «vars»;
  «fresh_right w1;»;
  «fresh_aux_1 $b1;»;
  «fresh_aux_2 $c1;»;
  «end;»;
  «proof»;
  «qed proof;»;
  «end transitivity;»;
  «reflexivity»;
  «proof»;
  «qed proof;»;
  «end reflexivity;»;
  «end;»;
  «AFTER END;»;
  ]))``
*)

Theorem parse_spec_aux_LENGTH[local]:
  ∀lim s ss acc res s' ss'.
  parse_spec_aux lim s ss acc = SOME (res,s',ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  ho_match_mp_tac parse_spec_aux_ind>>
  rpt strip_tac>>
  qpat_x_assum`parse_spec_aux _ _ _ _ = _` mp_tac>>
  simp[Once parse_spec_aux_def]>>
  rw[AllCaseEqs()]>>
  gvs[]
QED

Theorem parse_def_aux_LENGTH[local]:
  ∀lim s ss acc res s' ss'.
  parse_def_aux lim s ss acc = SOME (res,s',ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  Induct_on`ss`>>
  rw[parse_def_aux_def,AllCaseEqs()]>>
  res_tac>>
  simp[]
QED

Theorem parse_pre_order_LENGTH:
  parse_pre_order lim s ss = SOME (a,b,c,d,e,s',ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  rw[parse_pre_order_def,parse_vars_block_def,parse_spec_block_def,
     parse_trans_block_def,parse_trans_vars_def,parse_proof_block_def,
     parse_refl_block_def,parse_subproof_def,AllCaseEqs()]>>
  imp_res_tac parse_spec_aux_LENGTH>>
  imp_res_tac parse_def_aux_LENGTH>>
  imp_res_tac parse_subproof_aux_LENGTH>>
  gvs[]
QED

(* Parsing one cstep, or returning the line that is not one *)
Definition parse_cstep_def:
  (parse_cstep lim s [] = NONE) ∧
  (parse_cstep lim s (l::ls) =
    case parse_line l of
      NONE => SOME (INL l,s,ls)
    | SOME pl =>
      case name_pline lim pl s of
        NONE => NONE
      | SOME (pl1,s1) =>
      case pl1 of
        PbcHd c =>
        (case mk_npbc c of NONE => NONE
        | SOME c1 =>
          case parse_lsteps lim s1 ls of NONE => NONE
          | SOME (pf,s2,l2,rest) =>
            case check_mark_qed_id (INL «pbc») l2 of NONE => NONE
            | SOME id => SOME (INR (Sstep (Lstep (Con c1 pf id))),s2,rest))
      | RedHd c ss =>
        (case mk_npbc c of NONE => NONE
        | SOME c1 =>
          case parse_scope lim s1 ls of NONE => NONE
          | SOME (pf,s2,l2,rest) =>
            case check_mark_qed_id_opt (INL «red») l2 of NONE => NONE
            | SOME idopt => SOME (INR (Sstep (Red c1 ss pf idopt)),s2,rest))
      | DomHd c ss =>
        (case mk_npbc c of NONE => NONE
        | SOME c1 =>
          case parse_scope lim s1 ls of NONE => NONE
          | SOME (pf,s2,l2,rest) =>
            case check_mark_qed_id_opt (INL «dom») l2 of NONE => NONE
            | SOME idopt => SOME (INR (Dom c1 ss pf idopt),s2,rest))
      | DelcHd n ss =>
        (case parse_scope lim s1 ls of NONE => NONE
        | SOME (pf,s2,l2,rest) =>
          case check_mark_qed_id_opt (INL «delc») l2 of NONE => NONE
          | SOME idopt => SOME (INR (CheckedDelete n ss pf idopt),s2,rest))
      | OrdHd name =>
        (case parse_pre_order lim s1 ls of NONE => NONE
        | SOME (vars,gspec,f,pfr,pft,s2,rest) =>
          SOME (INR (StoreOrder name vars gspec f pfr pft),s2,rest))
      | ObjuHd b f =>
        (case normalise_obj (SOME f) of NONE => NONE
        | SOME f1 =>
          case parse_subproof lim s1 ls of NONE => NONE
          | SOME (pf,s2,l2,rest) =>
            case check_mark_qed_id_opt (INL «obju») l2 of
              SOME NONE => SOME (INR (ChangeObj b f1 pf),s2,rest)
            | _ => NONE)
      | PresHd b x c =>
        (case mk_npbc c of NONE => NONE
        | SOME c1 =>
          case parse_subproof lim s1 ls of NONE => NONE
          | SOME (pf,s2,l2,rest) =>
            case check_mark_qed_id_opt
              (if b then INL «preserved_add» else INL «preserved_rm») l2 of
              SOME NONE => SOME (INR (ChangePres b x c1 pf),s2,rest)
            | _ => NONE)
      | _ =>
        if is_lstep pl1 then
          case fin_lstep pl1 of NONE => NONE
          | SOME step => SOME (INR (Sstep (Lstep step)),s1,ls)
        else
          case fin_cstep pl1 of NONE => NONE
          | SOME cs => SOME (INR cs,s1,ls))
End

Theorem parse_cstep_LENGTH:
  parse_cstep lim s ss = SOME (res,s',ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  Cases_on`ss`>>
  rw[parse_cstep_def,parse_lsteps_def,parse_scope_def,parse_subproof_def,
     AllCaseEqs()]>>
  imp_res_tac parse_lsteps_aux_LENGTH>>
  imp_res_tac parse_scope_aux_LENGTH>>
  imp_res_tac parse_subproof_aux_LENGTH>>
  imp_res_tac parse_pre_order_LENGTH>>
  gvs[]
QED

(*
Definition parse_csteps_def:
  (parse_csteps f_ns ss acc =
    case parse_cstep f_ns ss of
      NONE => NONE
    | SOME (res,f_ns',rest) =>
      case res of
        INL s => SOME(REVERSE acc, s, f_ns', rest)
      | INR st =>
        parse_csteps f_ns' rest (st::acc))
Termination
  WF_REL_TAC `measure (LENGTH o FST o SND)`>>
  rw[parse_cstep_def]>>
  gvs[AllCaseEqs()]>>
  drule parse_sstep_length>>simp[]
  >-
    (drule parse_red_aux_length>>simp[])
  >-
  >-
    (drule parse_red_aux_length>>simp[])
  >-
    (drule parse_red_aux_length>>simp[])
End

Definition plainVar_nf_def:
  plainVar_nf s (u:unit) =
  if strlen s ≥ 1 ∧ strsub s 0 = #"x" then
    case mlint$fromNatString (substring s 1 (strlen s - 1)) of
      NONE => NONE
    | SOME n => SOME (n,())
  else
    NONE
End

(* Parse the tokenized pbf file *)
Definition parse_pbp_toks_def:
  parse_pbp_toks tokss =
  case parse_header tokss of
    SOME rest =>
      (case parse_csteps (plainVar_nf,()) rest [] of
        SOME (pf, s, f_ns', rest') =>
        SOME (pf, s, rest'))
  | NONE => NONE
End

Definition parse_pbp_def:
  parse_pbp strs = parse_pbp_toks (MAP toks strs)
End
*)
