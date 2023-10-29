(*
   Parsing interface for XLRUP
*)
open preamble miscTheory cnf_xorTheory xlrupTheory mlintTheory;

val _ = new_theory "xlrup_parsing";

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

Definition parse_rup_def:
  (parse_rup (cid::rest) =
  case cid of
    INL _ => NONE
  | INR n =>
    if n ≥ 0 then
      case parse_until_zero rest [] of
        NONE => NONE
      | SOME (c ,rest) =>
        (case parse_until_zero_nn rest [] of
          SOME (hints, []) =>
          SOME (RUP (Num (ABS n)) c hints)
        | _ => NONE)
    else NONE) ∧
  (parse_rup _ = NONE)
End

Definition parse_del_def:
  (parse_del (cid::first::rest) =
    case cid of INL i => NONE
    | INR _ =>
    (case parse_until_zero_nn rest [] of
     SOME (ls, []) => SOME (Del ls)
    | _ => NONE)) ∧
  (parse_del _ = NONE)
End

Definition parse_xdel_def:
  (parse_xdel (cid::first::rest) =
    if cid = INL (strlit "x")
    then
      (case parse_until_zero_nn rest [] of
       SOME (ls, []) => SOME (XDel ls)
      | _ => NONE)
    else NONE) ∧
  (parse_xdel _ = NONE)
End

Definition parse_xlrup_def:
  parse_xlrup ls =
  case parse_rup ls of SOME res => SOME res
  | NONE =>
  case parse_del ls of SOME res => SOME res
  | NONE =>
  case parse_xdel ls of SOME res => SOME res
  | NONE => NONE
End

Theorem parse_xlrup_wf:
  parse_xlrup ls = SOME xlrup ⇒
  wf_xlrup xlrup
Proof
  rw[parse_xlrup_def]>>
  gvs[AllCaseEqs()]>>
  cheat
QED

(* Mostly semantic!*)
Definition parse_xlrups_def:
  (parse_xlrups [] = SOME []) ∧
  (parse_xlrups (l::ls) =
    case parse_xlrup (MAP tokenize (tokens blanks l)) of
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
  strlit"12 d 1 5 3 0";
  strlit"13 -6 5 0 2 6 7 4 0";
  strlit"13 d 2 6 4 0";
  strlit"14 6 0 9 10 11 7 0";
  strlit"14 d 9 10 11 7 0";
  strlit"16 0 14 12 13 8 0";
  ]``;

val xlrups = rconc (EVAL ``THE (parse_xlrups ^(xlrupsraw))``);

val _ = export_theory ();
