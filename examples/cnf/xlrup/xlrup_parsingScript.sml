(*
   Parsing interface for XLRUP proofs
*)
Theory xlrup_parsing
Ancestors
  cnf ccnf syntax_helper xor xlrup_cnf xlrup mlint mlvector
Libs
  preamble

(* Parse nums until either a separator character c or the terminating
  zero. INL reports the separator case, INR the terminated case. *)
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

(* Parses the following format, where the [u ...] part is optional:
   (int list) 0 (num list) [u (num list)] 0 *)
Definition parse_u_rest_def:
  parse_u_rest rest =
  case parse_until_zero rest of
    NONE => NONE
  | SOME (c ,rest) =>
    (case parse_until_c_zero_nn «u» rest [] of
      SOME (INR (hints, [])) => SOME (c,hints,[])
    | SOME (INL (hints,rest)) =>
      (case parse_until_zero_nn rest of
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
      case parse_rup rest of NONE => NONE
      | SOME (c,hints) => SOME(Num (ABS n), c, hints)
    else NONE) ∧
  (parse_id_rest _ = NONE)
End

(* Parses the following format, where the [u ...] part is optional:
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

(* RUP or deletion (line prefix is a number) *)
Definition parse_rup_del_def:
  parse_rup_del n rest =
  if n ≥ 0 then
    case starts_with (INL «d») rest of
      INL rest =>
      (case parse_rup rest of NONE => NONE
      | SOME (c,hints) => SOME (RUP (Num (ABS n)) (Vector c) hints))
    | INR rest =>
      (* Del *)
      case parse_until_zero_nn rest of
       SOME (ls, []) => SOME (Del ls)
      | _ => NONE
  else NONE
End

(* XAdd or XDel (line prefix is "x") *)
Definition parse_xadd_xdel_def:
  parse_xadd_xdel rest =
  case starts_with (INL «d») rest of
    INL rest =>
    (* XAdd *)
    (case parse_id_u_rest rest of NONE => NONE
    | SOME (n,c,hints,chints) => SOME (XAdd n c hints chints))
  | INR rest =>
    (* XDel *)
    case parse_until_zero_nn rest of
       SOME (ls, []) => SOME (XDel ls)
    | _ => NONE
End

(* CFromX or XFromC (line prefix is "i", followed by a character) *)
Definition parse_imply_def:
  parse_imply rest =
  case rest of
  | INL s::rest =>
    if s = «x» then
      (* XFromC *)
      (case parse_id_rest rest of NONE => NONE
        | SOME (n,c,hints) => SOME (XFromC n c hints))
    else if s = «cx» then
      (* CFromX *)
      (case parse_id_rest rest of NONE => NONE
      | SOME (n,c,hints) => SOME (CFromX n c hints))
    else NONE
  | _ => NONE
End

Definition parse_xor_nomv_def:
  parse_xor_nomv xs =
  case parse_until_zero xs of
    SOME (x,[]) => SOME (MAP mk_lit x)
  | _ => NONE
End

(* Original constraint lines (line prefix is "o") *)
Definition parse_orig_def:
  parse_orig xs =
  case xs of
  | (c::INR n::rest) =>
  if n ≥ 0
  then
    let n = Num (ABS n) in
    if c = INL «x»
    then
      (* x [... 0] *)
      (case parse_xor_nomv rest of NONE => NONE
      | SOME c => SOME (XOrig n c))
    else NONE
  else NONE
  | _ => NONE
End

Definition parse_xlrup_def:
  (parse_xlrup [] = NONE) ∧
  (parse_xlrup (f::rest) =
  case f of
  | INR n => parse_rup_del n rest
  | INL c =>
    if c = «x»
    then
      parse_xadd_xdel rest
    else if c = «i»
    then
      parse_imply rest
    else if c = «o»
    then
      parse_orig rest
    else
       NONE)
End

Theorem parse_until_zero_nz_ilits:
  parse_until_zero ls = SOME(c, rest) ⇒
  nz_ilits c
Proof
  rw[nz_ilits_def]>>
  drule parse_until_zero_nz>>
  simp[EVERY_MEM]>>
  metis_tac[]
QED

Theorem parse_rup_nz_ilits:
  parse_rup ls = SOME (c,hints) ⇒
  nz_ilits c
Proof
  rw[parse_rup_def]>>
  gvs[AllCaseEqs()]>>
  metis_tac[parse_until_zero_nz_ilits]
QED

Theorem parse_id_rest_nz_ilits:
  parse_id_rest ls = SOME(n,c,hints) ⇒
  nz_ilits c
Proof
  Cases_on`ls`>>fs[parse_id_rest_def]>>
  gvs[AllCaseEqs()]>>
  metis_tac[parse_rup_nz_ilits,PAIR,FST,SND]
QED

Theorem parse_u_rest_nz_ilits:
  parse_u_rest ls = SOME (c,hints,chints) ⇒
  nz_ilits c
Proof
  rw[parse_u_rest_def]>>
  gvs[AllCaseEqs()]>>
  metis_tac[parse_until_zero_nz_ilits]
QED

Theorem parse_id_u_rest_nz_ilits:
  parse_id_u_rest ls = SOME(n,c,h0,hints) ⇒
  nz_ilits c
Proof
  Cases_on`ls`>>fs[parse_id_u_rest_def]>>
  gvs[AllCaseEqs()]>>
  metis_tac[parse_u_rest_nz_ilits,PAIR,FST,SND]
QED

Theorem parse_xor_nomv_nz_lit:
  parse_xor_nomv ls = SOME c ⇒
  EVERY nz_lit c
Proof
  rw[parse_xor_nomv_def]>>
  gvs[AllCaseEqs()]>>
  drule parse_until_zero_nz>>
  simp[EVERY_MAP,EVERY_MEM]>>
  metis_tac[nz_lit_mk_lit]
QED

Theorem parse_xlrup_wf:
  parse_xlrup ls = SOME line ⇒
  wf_xlrup line
Proof
  Cases_on`ls`>>rw[parse_xlrup_def]>>
  gvs[AllCaseEqs(),wf_xlrup_def,parse_xadd_xdel_def,parse_imply_def,
    parse_rup_del_def,parse_orig_def,toList_thm]>>
  metis_tac[parse_id_rest_nz_ilits,parse_rup_nz_ilits,
    parse_xor_nomv_nz_lit,parse_id_u_rest_nz_ilits]
QED

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
