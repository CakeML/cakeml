(*
  Syntactic print/parse helper files
*)
Theory syntax_helper
Ancestors
  misc cnf mlint mlstring
Libs
  preamble

(* Generic mlstring facts, belonging upstream in mlstringTheory *)

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

(* Parse an integer as a literal. *)
Definition mk_lit_def:
  mk_lit l =
  let n = Num (ABS l) in
  if l > 0 then Pos n else Neg n
End

(* The inverse conversion, from a literal to its integer encoding. *)
Definition to_ilit_def:
  to_ilit (l : num lit) =
  case l of
    Pos n => (&n):int
  | Neg n => -&n
End

Theorem to_ilit_NEQ_0:
  var_lit l ≠ 0 ⇒
  to_ilit l ≠ 0
Proof
  Cases_on`l`>>rw[to_ilit_def]
QED

(* to_ilit is inverted by the parser's literal reader *)
Theorem mk_lit_to_ilit:
  var_lit l ≠ 0 ⇒
  mk_lit (to_ilit l) = l
Proof
  Cases_on`l`>>rw[mk_lit_def,to_ilit_def]>>
  intLib.ARITH_TAC
QED

Theorem to_ilit_mk_lit:
  to_ilit (mk_lit l) = l
Proof
  rw[mk_lit_def,to_ilit_def]>>
  intLib.ARITH_TAC
QED

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

(* Force literals to be in maxvar *)
Definition check_maxvar_def:
  check_maxvar maxvar ls =
  EVERY (λl. var_lit l ≤ maxvar:num) ls
End

(* A single line of literals, forcing maxvar *)
Definition parse_lits_def:
  parse_lits maxvar ls =
  case parse_until_zero ls of
    SOME (ls,[]) =>
    let ls = MAP mk_lit ls in
    if check_maxvar maxvar ls
    then SOME ls
    else NONE
  | _ => NONE
End

(* Everything the parser accepts uses non-zero literals *)
Theorem nz_lit_mk_lit:
  i ≠ 0 ⇒ nz_lit (mk_lit i)
Proof
  rw[mk_lit_def]>>
  intLib.ARITH_TAC
QED

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

Theorem parse_lits_nz_lit:
  parse_lits maxvar ls = SOME c ⇒
  EVERY nz_lit c
Proof
  rw[parse_lits_def]>>
  gvs[AllCaseEqs()]>>
  drule parse_until_zero_nz>>
  simp[EVERY_MAP,EVERY_MEM]>>
  metis_tac[nz_lit_mk_lit]
QED

(* lines which are not comments don't start with a single "c" *)
Definition nocomment_line_def:
  (nocomment_line (INL c::cs) = (c ≠ «c»)) ∧
  (nocomment_line _ = T)
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
  let nocomments = FILTER nocomment_line tokss in
  case nocomments of
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
  Printing helpers.
***)

Definition print_lit_def:
  (print_lit (Pos n) = toString n) ∧
  (print_lit (Neg n) = «-» ^ toString n)
End

(* Print a list of literals with optional terminator char. *)
Definition print_lits_def:
  print_lits (term:char) ls =
    let ls = SNOC («0» ^ toString term) (MAP print_lit ls) in
    concatWith « » ls
End

Theorem print_lits_nil:
  print_lits term [] = «0» ^ toString term
Proof
  rw[print_lits_def,concatWith_def,mllistTheory.intersperse_def]>>
  EVAL_TAC
QED

Theorem print_lits_cons:
  print_lits term (l::ls) =
  print_lit l ^ « » ^ print_lits term ls
Proof
  rw[print_lits_def,concatWith_def]>>
  Cases_on`ls`>>
  simp[mllistTheory.intersperse_def]>>
  EVAL_TAC>>
  simp[STRCAT_ASSOC]>>
  simp[STRCAT_ASSOC]
QED

(* Maximum of a list of numbers *)
Definition max_list_def:
  (max_list k [] = k) ∧
  (max_list k (x::xs) = max_list (MAX k x) xs)
End

Theorem max_list_max:
  ∀ls k.
  k ≤ max_list k ls ∧
  EVERY (λn. n ≤ max_list k ls)  ls
Proof
  Induct>>rw[max_list_def]>>
  first_x_assum(qspec_then`MAX k h` mp_tac)>>
  simp[]
QED

Theorem le_max_list:
  (∃l. v ≤ l ∧ MEM l ls) ⇒
  v ≤ max_list k ls
Proof
  rw[]>>
  assume_tac (SPEC_ALL max_list_max)>>
  rw[EVERY_MEM]>>
  first_x_assum drule>>fs[]
QED

Definition print_header_line_def:
  print_header_line v len =
  «p cnf » ^ toString v ^ « » ^ toString len ^ «\n»
End

(***
  Round trip: parsing a printed line returns it unchanged.
***)

Theorem tokens_unchanged:
  EVERY ($~ o P) (explode ls) ∧ ¬ NULL (explode ls) ⇒
  tokens P ls = [ls]
Proof
  rw[] >> drule TOKENS_unchanged>>
  simp[]>>
  simp[GSYM mlstringTheory.TOKENS_eq_tokens]
QED

Theorem isDigit_not_blanks[local]:
  isDigit c ==> ~ blanks c
Proof
  CCONTR_TAC>>fs [blanks_def]>>fs [isDigit_def]
QED

Theorem blanks_thms[simp]:
  (blanks #"\n") ∧
  (blanks #" ") ∧
  (¬blanks #"-")
Proof
  EVAL_TAC
QED

Theorem tokens_blanks_print_lit:
  tokens blanks (print_lit l) = [print_lit l]
Proof
  match_mp_tac tokens_unchanged>>
  Cases_on`l`>>
  simp[print_lit_def]>>
  rename1`toString n`>>
  Cases_on`toString n`>>
  `~NULL s` by
    (drule num_to_str_imp_cons>>rw[]>>fs[])>>
  simp[]>>
  irule listTheory.EVERY_MONOTONIC >>
  irule_at Any num_to_str_every>>
  asm_exists_tac>>simp[GSYM isDigit_def, isDigit_not_blanks]
QED

Theorem print_lit_alt:
  n ≠ 0 ⇒
  (print_lit (Pos n) = int_to_string (#"-") (&n)) ∧
  (print_lit (Neg n) = int_to_string (#"-") (-&n))
Proof
  rw[print_lit_def,int_to_string_thm,num_to_str_thm]>>
  simp[strcat_def,concat_def]
QED

Theorem fromString_print_lit:
  nz_lit h ⇒
  fromString (print_lit h) = SOME (to_ilit h)
Proof
  Cases_on`h`>>rw[]>>
  drule print_lit_alt>>simp[]>>
  rw[to_ilit_def]
QED

Theorem tokenize_print_lit[simp]:
  nz_lit n ⇒
  tokenize (print_lit n) = INR (to_ilit n)
Proof
  rw[tokenize_def]>>
  drule fromString_print_lit>>rw[]
QED

Theorem parse_until_zero_aux_print_lits:
  ∀ys acc.
  EVERY nz_lit ys ∧ blanks c
  ⇒
  parse_until_zero_aux (toks (print_lits c ys ^ rest)) acc =
    SOME (REVERSE acc ++ MAP to_ilit ys,toks rest)
Proof
  simp[toks_def]>>
  Induct>>rw[print_lits_nil,print_lits_cons]
  >- (
    drule mlstringTheory.tokens_append>>simp[]>>
    PURE_REWRITE_TAC[GSYM strcat_assoc]>>
    disch_then (fn th => simp[th])>>
    EVAL_TAC)>>
  `blanks #" " ∧ toString #" " = « »` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  PURE_REWRITE_TAC[GSYM strcat_assoc]>>
  disch_then (fn th => simp[th])>>
  simp[tokens_blanks_print_lit]>>
  gvs[parse_until_zero_aux_def]>>
  DEP_REWRITE_TAC[tokenize_print_lit]>>
  simp[]>>
  `to_ilit h ≠ 0` by metis_tac[to_ilit_NEQ_0]>>
  simp[]
QED

Theorem parse_lits_print_lits:
  EVERY nz_lit ys ∧
  EVERY (λl. var_lit l ≤ maxvar) ys
  ⇒
  parse_lits maxvar (toks (print_lits #"\n" ys)) = SOME ys
Proof
  strip_tac>>
  simp[parse_lits_def,parse_until_zero_def]>>
  `print_lits #"\n" ys = print_lits #"\n" ys ^ «»` by simp[strcat_nil]>>
  pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th])>>
  DEP_REWRITE_TAC[parse_until_zero_aux_print_lits]>>
  simp[]>>
  `toks «» = []` by EVAL_TAC>>
  simp[]>>
  `MAP mk_lit (MAP to_ilit ys) = ys` by (
    simp[MAP_MAP_o,o_DEF,MAP_EQ_ID]>>
    gvs[EVERY_MEM]>>
    metis_tac[mk_lit_to_ilit])>>
  simp[check_maxvar_def]
QED

Theorem FILTER_nocomment_print_lits:
  EVERY (EVERY nz_lit) ls ⇒
  FILTER nocomment_line
    (MAP toks (MAP (print_lits #"\n") ls)) =
    (MAP toks (MAP (print_lits #"\n") ls))
Proof
  simp[FILTER_EQ_ID,EVERY_MAP,EVERY_MEM]>>
  rw[]>>
  Cases_on`x`>>simp[print_lits_nil,print_lits_cons]
  >- EVAL_TAC >>
  `blanks #" " ∧ toString #" " = « »` by EVAL_TAC>>
  first_x_assum drule>>
  simp[DISJ_IMP_THM,FORALL_AND_THM]>>rw[]>>
  simp[toks_def]>>
  drule mlstringTheory.tokens_append>>simp[]>>
  PURE_REWRITE_TAC[GSYM strcat_assoc]>>
  disch_then (fn th => simp[th])>>
  simp[tokens_blanks_print_lit]>>
  DEP_REWRITE_TAC[tokenize_print_lit]>>
  simp[nocomment_line_def]
QED

Theorem tokens_blanks_toString:
  tokens blanks (toString h) = [toString h]
Proof
  match_mp_tac tokens_unchanged>>
  Cases_on`toString h`>>
  `~NULL s` by
    (drule num_to_str_imp_cons>>rw[]>>fs[])>>
  simp[]>>
  irule listTheory.EVERY_MONOTONIC >>
  irule_at Any num_to_str_every>>
  asm_exists_tac>>simp[GSYM isDigit_def, isDigit_not_blanks]
QED

Theorem tokenize_toString[simp]:
  tokenize (toString n) = INR (&n)
Proof
  rw[tokenize_def,num_to_str_def]
QED

Theorem fromString_toString_num:
  mlint$fromString ((toString (n:num)):mlstring) = SOME (&n)
Proof
  rw[num_to_str_def]
QED

Theorem parse_header_line_print_header_line:
  parse_header_line (toks (print_header_line v len)) = SOME(v,len)
Proof
  rw[print_header_line_def, toks_def]>>
  qmatch_goalsub_abbrev_tac`aa ^ bb ^ _ ^ cc ^ dd`>>
  `blanks #" " ∧ toString #" " = « »` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  `aa = «p» ^ « » ^ «cnf» ^ « »` by
    (fs[Abbr`aa`]>>EVAL_TAC)>>
  strip_tac>>
  first_assum(qspecl_then[`aa ^ bb`,`cc ^ dd`] assume_tac)>>fs[]>>
  `cc ^ dd = cc ^ dd ^ «»` by EVAL_TAC>>
  pop_assum SUBST_ALL_TAC>>
  `blanks #"\n" ∧ toString #"\n" = «\n»` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  unabbrev_all_tac>>
  rw[]>>
  `tokens blanks «p» = [«p»]` by EVAL_TAC>>
  `tokens blanks «cnf» = [«cnf»]` by EVAL_TAC>>
  `tokens blanks «» = []` by EVAL_TAC>>
  simp[tokens_blanks_toString]>>
  simp[tokenize_def,parse_header_line_def]>>
  CONJ_TAC >- EVAL_TAC>>
  simp[fromString_toString_num]>>
  intLib.ARITH_TAC
QED

Theorem print_header_line_first:
  ∃ls. tokens blanks (print_header_line a b) =
  «p»::ls
Proof
  rw[print_header_line_def]>>
  qmatch_goalsub_abbrev_tac`aa ^ bb ^ _ ^ dd ^ ee`>>
  `aa = «p» ^ « » ^ «cnf» ^ « »` by
    (fs[Abbr`aa`]>>EVAL_TAC)>>
  simp[]>>
  PURE_REWRITE_TAC[GSYM mlstringTheory.strcat_assoc]>>
  PURE_REWRITE_TAC[Once mlstringTheory.strcat_assoc]>>
  `blanks #" " ∧ toString #" " = « »` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  `tokens blanks «p» = [«p»]` by EVAL_TAC>>
  simp[]
QED


(***
  Less restrictive helpers for print/parse.
  This is mainly for implementing proof parsers in ASCII.
***)

Definition fromString_unsafe_def:
  fromString_unsafe str =
    if strlen str = 0
    then 0i
    else if strsub str 0 = #"-"
      then ~&fromChars_unsafe (strlen str - 1)
                              (substring str 1 (strlen str - 1))
      else &fromChars_unsafe (strlen str) str
End

Definition is_int_def:
  is_int c ⇔
  (#"0" ≤ c ∧ c ≤ #"9") ∨ c = #"-"
End

(* Tokenizes as an integer if first character is numeric or "-" *)
Definition tokenize_fast_def:
  tokenize_fast (s:mlstring) =
  if strlen s = 0 then INL s
  else if is_int (strsub s 0) then INR (fromString_unsafe s)
  else INL s
End

Definition toks_fast_def:
  toks_fast s = MAP tokenize_fast (tokens blanks s)
End

(***
  Binary format parser
***)

Definition parse_vb_num_aux_def:
  parse_vb_num_aux (s:mlstring) (i:num) (len:num) (ex:num) (n:num) =
  if i < len then
    let v = ORD (strsub s i) in
      if v >= 128 then (* msb is set *)
        parse_vb_num_aux s (i+1) len (ex*128) ((v-128)*ex+n)
      else
        ((v*ex+n),i + 1)
  else (0, i) (* should not happen *)
Termination
  WF_REL_TAC` measure (λ(x,s,i,r). i-s)`
End

Theorem parse_vb_num_aux_i:
 !s i len ex n m i'.
  m <> 0 /\
  (m,i') = parse_vb_num_aux s i len ex n ==>
  i < len /\ i < i'
Proof
 ho_match_mp_tac parse_vb_num_aux_ind >>
 rpt GEN_TAC >> strip_tac >>
 simp[Once parse_vb_num_aux_def] >>
 rw[] >> fs[] >>
 first_x_assum (drule_at (Pos last)) >>
 rw[] >>
 fs[Once parse_vb_num_aux_def,AllCaseEqs()]
QED

Definition parse_vb_num_def:
  parse_vb_num s offset len =
  parse_vb_num_aux s offset len 1 0
End

Definition parse_vb_int_def:
  parse_vb_int s offset len =
  let (m,i) = parse_vb_num s offset len in
  let v =
      (if m = 0 then 0i
      else if m MOD 2 = 0n
      then (&(m DIV 2):int)
      else (-&(m DIV 2):int)) in
  (v,i)
End

Definition parse_vb_nums_aux_def:
  parse_vb_nums_aux (s:mlstring) (i:num) (len:num) (acc:num list) =
  let (m,i) = parse_vb_num s i len in
  if m = 0
  then
    acc
  else
    parse_vb_nums_aux s i len (m::acc)
Termination
  WF_REL_TAC` measure (λ(x,s,i,r). i-s)`>>
  rw[]>> fs[parse_vb_num_def] >>
  drule_all parse_vb_num_aux_i >>
  fs[]
End

(* Clausify reverses the order of the input *)
Definition clausify_aux_def:
  (clausify_aux [] acc = acc) ∧
  (clausify_aux (x::xs) acc =
    let v =
      (if x MOD 2 = 0n
      then (&(x DIV 2):int)
      else (-&(x DIV 2):int)) in
      clausify_aux xs (v::acc))
End

Definition clausify_def:
  clausify cls = clausify_aux cls []
End

(* Decode a doubled literal: even is positive, odd negative *)
Definition vb_ilit_def:
  vb_ilit (m:num) =
  if m MOD 2 = 0n
  then (&(m DIV 2):int)
  else (-&(m DIV 2):int)
End

(* Reads doubled literals until the terminating zero, decoding as it
  goes. The result is in reverse order with respect to the input. *)
Definition parse_vb_ilits_def:
  parse_vb_ilits (s:mlstring) (i:num) (len:num) (acc:int list) =
  let (m,i) = parse_vb_num s i len in
  if m = 0
  then
    acc
  else
    parse_vb_ilits s i len (vb_ilit m::acc)
Termination
  WF_REL_TAC` measure (λ(x,s,i,r). i-s)`>>
  rw[]>> fs[parse_vb_num_def] >>
  drule_all parse_vb_num_aux_i >>
  fs[]
End

(* Other ASCII syntax parsing tools *)

(* Parse nums until the next zero and returns. *)
Definition parse_until_zero_nn_aux_def:
  (parse_until_zero_nn_aux [] acc = NONE) ∧
  (parse_until_zero_nn_aux (x::xs) acc =
    case x of
      INL _ => NONE
    | INR l =>
    if l = 0:int then
      SOME (REVERSE acc, xs)
    else
      if l > 0 then parse_until_zero_nn_aux xs (Num (ABS l)::acc)
      else NONE
  )
End

Definition parse_until_zero_nn_def:
  parse_until_zero_nn ls =
    parse_until_zero_nn_aux ls []
End

(* If a line starts with the character,
  return INR without that char
  otherwise INL or line unchanged *)
Definition starts_with_def:
  (starts_with s (first::rest) =
  if first = s
  then
    INR rest
  else INL (first::rest)) ∧
  (starts_with s [] = INL [])
End

(* The RUP hint format, shared by the LRUP and XLRUP proof formats:
   (int list) 0 (num list) 0 *)
Definition parse_rup_def:
  parse_rup rest =
  case parse_until_zero rest of
    NONE => NONE
  | SOME (c ,rest) =>
    (case parse_until_zero_nn rest of
      SOME (hints, []) => SOME (c,hints)
    | _ => NONE)
End

