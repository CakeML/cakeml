(*
   Parsing interface for XLRUP
*)
open preamble miscTheory cnf_xorTheory xlrupTheory mlintTheory;

val _ = new_theory "xlrup_parsing";

val fromString_unsafe_def = Define`
  fromString_unsafe str =
    if strlen str = 0
    then 0i
    else if strsub str 0 = #"-"
      then ~&fromChars_unsafe (strlen str - 1)
                              (substring str 1 (strlen str - 1))
      else &fromChars_unsafe (strlen str) str`;

(* lowercase alphabet *)
Definition is_lowercase_def:
  is_lowercase c ⇔
  #"a" ≤ c ∧ c ≤ #"z"
End

val tokenize_fast_def = Define`
  tokenize_fast (s:mlstring) =
  if strlen s = 0 then INL s
  else if is_lowercase (strsub s 0) then INL s
  else INR (fromString_unsafe s)`

val toks_fast_def = Define`
  toks_fast s = MAP tokenize_fast (tokens blanks s)`

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

Definition parse_until_zero_nn_def:
  (parse_until_zero_nn [] acc = NONE) ∧
  (parse_until_zero_nn (x::xs) acc =
    case x of
      INL _ => NONE
    | INR l =>
    if l = 0:int then
      SOME (REVERSE acc, xs)
    else
      if l > 0 then parse_until_zero_nn xs (Num (ABS l)::acc)
      else NONE
  )
End

(* Parses the following format:
   (int list) 0 (num list) 0 *)
Definition parse_rest_def:
  parse_rest rest =
  case parse_until_zero rest [] of
    NONE => NONE
  | SOME (c ,rest) =>
    (case parse_until_zero_nn rest [] of
      SOME (hints, []) => SOME (c,hints)
    | _ => NONE)
End

(* Parses the following format:
   num (int list) 0 (num list) 0 *)
Definition parse_id_rest_def:
  (parse_id_rest (id::rest) =
  case id of INL _ => NONE
  | INR n =>
    if n ≥ 0 then
      case parse_rest rest of NONE => NONE
      | SOME (c,hints) => SOME(Num (ABS n), c, hints)
    else NONE) ∧
  (parse_id_rest _ = NONE)
End

(* Parses the following format:
  d (num list) *)
Definition parse_del_def:
  (parse_del (first::rest) =
    if first = INL (strlit "d")
    then
      case parse_until_zero_nn rest [] of
       SOME (ls, []) => SOME ls
      | _ => NONE
    else NONE) ∧
  (parse_del _ = NONE)
End

Definition parse_xlrup_def:
  (parse_xlrup [] = NONE) ∧
  (parse_xlrup (f::rest) =
  case f of
  | INR n =>
    if n ≥ 0 then
      case parse_del rest of
        (* RUP *)
        NONE =>
        (case parse_rest rest of NONE => NONE
        | SOME (c,hints) => SOME (RUP (Num (ABS n)) c hints))
        (* Del *)
      | SOME ls => SOME (Del ls)
    else NONE
  | INL c =>
    if c = strlit"x"
    then
      case parse_del rest of
        (* XAdd *)
        NONE =>
        (case parse_id_rest rest of NONE => NONE
        | SOME (n,c,hints) => SOME (XAdd n c hints))
        (* XDel *)
      | SOME ls => SOME (XDel ls)
    else NONE)
End

Theorem parse_xlrup_wf:
  parse_xlrup ls = SOME line ⇒
  wf_xlrup line
Proof
  rw[parse_xlrup_def]>>
  gvs[AllCaseEqs()]>>
  cheat
QED

(* Mostly semantic!*)
Definition parse_xlrups_def:
  (parse_xlrups [] = SOME []) ∧
  (parse_xlrups (l::ls) =
    case parse_xlrup (toks_fast l) of
      NONE => NONE
    | SOME step =>
      (case parse_xlrups ls of
        NONE => NONE
      | SOME ss => SOME (step :: ss))
    )
End

Theorem parse_xlrups_wf:
  ∀ls xlrups.
  parse_xlrups ls = SOME xlrups ⇒
  EVERY wf_xlrup xlrups
Proof
  Induct>>fs[parse_xlrups_def]>>
  ntac 2 strip_tac>>
  every_case_tac>>fs[]>>
  rw[]>>simp[]>>
  drule parse_xlrup_wf>>
  simp[]
QED

val xlrupsraw = ``[
  strlit"8 d 0";
  strlit"x d 1 2 0";
  strlit"9 6 1 0 1 2 8 0";
  strlit"10 6 2 0 3 4 8 0";
  strlit"11 6 3 0 5 6 8 0";
  strlit"12 -6 4 0 1 5 7 3 0";
  strlit"x 1234 -6 4 0 1 5 7 3 0";
  strlit"12 d 1 5 3 0";
  strlit"13 -6 5 0 2 6 7 4 0";
  strlit"13 d 2 6 4 0";
  strlit"14 6 0 9 10 11 7 0";
  strlit"14 d 9 10 11 7 0";
  strlit"16 0 14 12 13 8 0";
  ]``;

val xlrups = rconc (EVAL ``THE (parse_xlrups ^(xlrupsraw))``);

val _ = export_theory ();
