(*
  Syntactic print/parse helper files
*)
Theory syntax_helper
Ancestors
  misc cnf mlint mlstring
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

(* Parse an integer as a literal. *)
Definition mk_lit_def:
  mk_lit l =
  let n = Num (ABS l) in
  if l > 0 then Pos n else Neg n
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

(* lines which are not comments don't start with a single "c" *)
Definition nocomment_line_def:
  (nocomment_line (INL c::cs) = (c ≠ strlit "c")) ∧
  (nocomment_line _ = T)
End

(***
  Printing helpers.
***)

Definition print_lit_def:
  (print_lit (Pos n) = toString n) ∧
  (print_lit (Neg n) = strlit"-" ^ toString n)
End

(* Print a list of literals with optional terminator char. *)
Definition print_lits_def:
  print_lits (term:char) ls =
    let ls = SNOC (strlit"0" ^ str term) (MAP print_lit ls) in
    concatWith (strlit" ") ls
End


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

