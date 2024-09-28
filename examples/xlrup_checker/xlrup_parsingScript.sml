(*
   Parsing interface for XLRUP
*)
open preamble miscTheory cnf_xorTheory xlrupTheory mlintTheory;

val _ = new_theory "xlrup_parsing";

Definition fromString_unsafe_def:
  fromString_unsafe str =
    if strlen str = 0
    then 0i
    else if strsub str 0 = #"-"
      then ~&fromChars_unsafe (strlen str - 1)
                              (substring str 1 (strlen str - 1))
      else &fromChars_unsafe (strlen str) str
End

(* lowercase alphabet *)
Definition is_lowercase_def:
  is_lowercase c ⇔
  #"a" ≤ c ∧ c ≤ #"z"
End

Definition tokenize_fast_def:
  tokenize_fast (s:mlstring) =
  if strlen s = 0 then INL s
  else if is_lowercase (strsub s 0) then INL s
  else INR (fromString_unsafe s)
End

Definition toks_fast_def:
  toks_fast s = MAP tokenize_fast (tokens blanks s)
End

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

Definition parse_until_c_zero_nn_def:
  (parse_until_c_zero_nn c [] acc = NONE) ∧
  (parse_until_c_zero_nn c (x::xs) acc =
    case x of
      INL s => if s = c then SOME (INL (REVERSE acc, xs)) else NONE
    | INR l =>
    if l = 0:int then
      SOME (INR (REVERSE acc, xs))
    else
      if l > 0 then parse_until_c_zero_nn c xs (Num (ABS l)::acc)
      else SOME (INL (REVERSE acc, xs))
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

(* Parses the following format [u] part optional:
   (int list) 0 (num list) [u (num list)] 0 *)
Definition parse_u_rest_def:
  parse_u_rest rest =
  case parse_until_zero rest [] of
    NONE => NONE
  | SOME (c ,rest) =>
    (case parse_until_c_zero_nn (strlit"u") rest [] of
      SOME (INR (hints, [])) => SOME (c,hints,[])
    | SOME (INL (hints,rest)) =>
      (case parse_until_zero_nn rest [] of
          SOME (chints, []) => SOME (c,hints,chints)
        | _ => NONE)
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

(* Parses the following format [u] part optional:
  num (int list) 0 (num list) [u (num list)] 0 *)
Definition parse_id_u_rest_def:
  (parse_id_u_rest (id::rest) =
  case id of INL _ => NONE
  | INR n =>
    if n ≥ 0 then
      case parse_u_rest rest of NONE => NONE
      | SOME (c,hints,chints) => SOME(Num (ABS n), c, hints,chints)
    else NONE) ∧
  (parse_id_u_rest _ = NONE)
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

(* RUP or deletion *)
Definition parse_rup_del_def:
  parse_rup_del n rest =
  if n ≥ 0 then
    case starts_with (INL (strlit "d")) rest of
      INL rest =>
      (case parse_rest rest of NONE => NONE
      | SOME (c,hints) => SOME (RUP (Num (ABS n)) c hints))
    | INR rest =>
      (* Del *)
      case parse_until_zero_nn rest [] of
       SOME (ls, []) => SOME (Del ls)
      | _ => NONE
  else NONE
End

(* XAdd or Xdel *)
Definition parse_xadd_xdel_def:
  parse_xadd_xdel rest =
  case starts_with (INL (strlit "d")) rest of
    INL rest =>
    (* XAdd *)
    (case parse_id_u_rest rest of NONE => NONE
    | SOME (n,c,hints,chints) => SOME (XAdd n c hints chints))
  | INR rest =>
    (* XDel *)
    case parse_until_zero_nn rest [] of
       SOME (ls, []) => SOME (XDel ls)
    | _ => NONE
End

(* CFromX or XFromC *)
Definition parse_cfromx_xfromc_def:
  parse_cfromx_xfromc rest =
  case starts_with (INL (strlit "x")) rest of
    INL rest =>
    (* CFromX *)
    (case parse_id_rest rest of NONE => NONE
      | SOME (n,c,hints) => SOME (CFromX n c hints))
  | INR rest =>
    (* XFromC *)
    (case parse_id_rest rest of NONE => NONE
        | SOME (n,c,hints) => SOME (XFromC n c hints))
End

(* Copied from cnf_xor *)
Definition parse_lits_aux_nomv_def:
  (parse_lits_aux_nomv [] (acc:lit list) = NONE) ∧
  (parse_lits_aux_nomv [c] acc =
    if c = INR 0i then SOME (REVERSE acc) else NONE) ∧
  (parse_lits_aux_nomv (x::xs) acc =
    case x of
      INR l =>
      let n = Num (ABS l) in
      let v = if l > 0 then Pos n else Neg n in
      if n = 0 then NONE
      else parse_lits_aux_nomv xs (v::acc)
    | INL (_:mlstring) => NONE)
End

Definition parse_id_xor_nomv_def:
  parse_id_xor_nomv xs =
  case xs of
  | (c::INR n::cs) =>
  if c = INL (strlit "x") ∧ n ≥ 0
  then
    case parse_lits_aux_nomv cs [] of
      SOME x => SOME (Num (ABS n), x)
    | _ => NONE
  else NONE
  | _ => NONE
End

(* XOrig *)
Definition parse_xorig_def:
  parse_xorig rest =
  (* o x [... 0] *)
  (case parse_id_xor_nomv rest of NONE => NONE
  | SOME (n, c) => SOME (XOrig n c))
End

Definition parse_xlrup_def:
  (parse_xlrup [] = NONE) ∧
  (parse_xlrup (f::rest) =
  case f of
  | INR n => parse_rup_del n rest
  | INL c =>
    if c = strlit"x"
    then
      parse_xadd_xdel rest
    else
    if c = strlit"i"
    then
      parse_cfromx_xfromc rest
    else
    if c = strlit"o"
    then
      parse_xorig rest
    else
       NONE)
End

Theorem parse_until_zero_wf_clause:
  ∀ls acc.
  parse_until_zero ls acc = SOME(c, rest) ∧
  wf_clause acc ⇒
  wf_clause c
Proof
  Induct>>rw[parse_until_zero_def]>>
  gvs[AllCaseEqs(),wf_clause_def]>>
  first_x_assum match_mp_tac>>
  last_x_assum (irule_at Any)>>
  fs[]
QED

Theorem parse_rest_wf_clause:
  parse_rest ls = SOME (c,hints) ⇒
  wf_clause c
Proof
 rw[parse_rest_def]>>
 gvs[AllCaseEqs()]>>
 drule parse_until_zero_wf_clause>>
 fs[wf_clause_def]
QED

Theorem parse_id_rest_wf_clause:
  parse_id_rest ls = SOME(n,c,hints) ⇒
  wf_clause c
Proof
  Cases_on`ls`>>fs[parse_id_rest_def]>>
  gvs[AllCaseEqs()]>>
  metis_tac[parse_rest_wf_clause,PAIR,FST,SND]
QED

Theorem parse_lits_aux_nomv_nz_lit:
  ∀cs acc acc'.
  parse_lits_aux_nomv cs acc = SOME acc' ∧
  EVERY nz_lit acc ⇒
  EVERY nz_lit acc'
Proof
  ho_match_mp_tac parse_lits_aux_nomv_ind>>
  rw[parse_lits_aux_nomv_def]>>
  gvs[AllCaseEqs()]>>
  every_case_tac>>fs[]
QED

Theorem parse_id_xor_nomv_nz_lit:
  parse_id_xor_nomv ls = SOME (n,c) ⇒
  EVERY nz_lit c
Proof
  simp[parse_id_xor_nomv_def]>>
  rw[AllCaseEqs()]>>
  drule parse_lits_aux_nomv_nz_lit>>
  simp[]
QED

Theorem parse_xlrup_wf:
  parse_xlrup ls = SOME line ⇒
  wf_xlrup line
Proof
  Cases_on`ls`>>rw[parse_xlrup_def]>>
  gvs[AllCaseEqs(),wf_xlrup_def,parse_xadd_xdel_def,parse_cfromx_xfromc_def,parse_rup_del_def,parse_xorig_def]>>
  metis_tac[parse_id_rest_wf_clause,parse_rest_wf_clause,parse_id_xor_nomv_nz_lit]
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
  strlit"o x 5 -1 1 2 3 0";
  strlit"12 d 1 5 3 0";
  strlit"13 -6 5 0 2 6 7 4 0";
  strlit"13 d 2 6 4 0";
  strlit"14 6 0 9 10 11 7 0";
  strlit"14 d 9 10 11 7 0";
  strlit"16 0 14 12 13 8 0";
  strlit"i 17 0 14 12 13 8 0";
  strlit"i x 17 0 14 12 13 8 0";
  ]``;

val xlrups = rconc (EVAL ``THE (parse_xlrups ^(xlrupsraw))``);

val _ = export_theory ();
