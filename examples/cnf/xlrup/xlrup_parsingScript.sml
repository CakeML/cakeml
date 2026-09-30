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

(***
  Parser for the binary XLRUP format.

  Records are chunks terminated by a zero byte, as in the binary LRUP
  format, whose a and d records are reused unchanged. An XOR record
  starts with x and a kind byte:

    x o <id> <lits> 0                       original XOR
    x a <id> <lits> 0   <xids> 0   <cids> 0 XOR addition, then unit propagation
    x d <xids> 0                            XOR deletion
    x c <id> <lits> 0   <xids> 0            clause from XORs
    x i <id> <lits> 0   <cids> 0            XOR from clauses
 ***)

(* A first chunk whose record owes further hint chunks *)
Datatype:
  xlrupb_rest =
  | BRup num vcclause
  | BXAdd num rawxor
  | BCFromX num cclause
  | BXFromC num rawxor
End

Definition parse_xlrupb_chunk_def:
  parse_xlrupb_chunk s =
  if strlen s = 0 then NONE
  else
  let c = strsub s 0 in
  if c = #"x"
  then
    if strlen s < 2 then NONE
    else
    let k = strsub s 1 in
    if k = #"d" then SOME (INL (XDelvb s))
    else
    let len = strlen s in
    let (m,i) = parse_vb_num s 2 len in
    if m = 0 ∨ m MOD 2 ≠ 0
    then NONE
    else
    let n = m DIV 2 in
    let ls = parse_vb_ilits s i len [] in
    if k = #"o" then SOME (INL (XOrig n (MAP mk_lit (REVERSE ls))))
    else if k = #"a" then SOME (INR (BXAdd n ls))
    else if k = #"c" then SOME (INR (BCFromX n ls))
    else if k = #"i" then SOME (INR (BXFromC n ls))
    else NONE
  else if c = #"d" then SOME (INL (Delvb s))
  else if c = #"a"
  then
    let len = strlen s in
    let (m,i) = parse_vb_num s 1 len in
    if m = 0 ∨ m MOD 2 ≠ 0
    then NONE
    else SOME (INR (BRup (m DIV 2) (Vector (parse_vb_ilits s i len []))))
  else NONE
End

(* The record whose first chunk is l, taking the chunks it owes from
  ls: NONE on a parse failure, otherwise the step and the unread chunks *)
Definition parse_xlrupb_rest_def:
  parse_xlrupb_rest l ls =
  case parse_xlrupb_chunk l of
    NONE => NONE
  | SOME (INL step) => SOME (step, ls)
  | SOME (INR (BRup n C)) =>
    (case ls of
      [] => NONE
    | h::rest => SOME (RUPvb n C h, rest))
  | SOME (INR (BXAdd n X)) =>
    (case ls of
      h1::h2::rest => SOME (XAddvb n X h1 h2, rest)
    | _ => NONE)
  | SOME (INR (BCFromX n C)) =>
    (case ls of
      [] => NONE
    | h::rest => SOME (CFromXvb n C h, rest))
  | SOME (INR (BXFromC n X)) =>
    (case ls of
      [] => NONE
    | h::rest => SOME (XFromCvb n X h, rest))
End

(* One record's worth of chunks: NONE on a parse failure, SOME NONE at
  end of file, and otherwise the step together with the unread chunks *)
Definition parse_xlrupb_one_def:
  parse_xlrupb_one lines =
  case lines of
    [] => SOME NONE
  | l::ls => OPTION_MAP SOME (parse_xlrupb_rest l ls)
End

Theorem parse_xlrupb_one_LENGTH:
  parse_xlrupb_one lines = SOME (SOME (step,rest)) ⇒
  LENGTH rest < LENGTH lines
Proof
  rw[parse_xlrupb_one_def,parse_xlrupb_rest_def]>>
  gvs[AllCaseEqs()]
QED

Definition parse_xlrupsb_def:
  parse_xlrupsb lines =
  case parse_xlrupb_one lines of
    NONE => NONE
  | SOME NONE => SOME []
  | SOME (SOME (step,rest)) =>
    (case parse_xlrupsb rest of
      NONE => NONE
    | SOME ss => SOME (step :: ss))
Termination
  WF_REL_TAC` measure LENGTH`>>
  rw[]>>
  drule parse_xlrupb_one_LENGTH>>
  simp[]
End

(* The literals a first chunk carries are non-zero, whichever record it
  starts *)
Theorem parse_xlrupb_chunk_wf:
  parse_xlrupb_chunk l = SOME res ⇒
  case res of
    INL step => wf_xlrup step
  | INR (BRup n C) => nz_ilits (toList C)
  | INR (BXAdd n X) => T
  | INR (BCFromX n C) => nz_ilits C
  | INR (BXFromC n X) => nz_ilits X
Proof
  rw[parse_xlrupb_chunk_def]>>
  rpt (pairarg_tac>>gvs[])>>
  gvs[AllCaseEqs(),wf_xlrup_def]>>
  gvs[nz_ilits_def,toList_thm,EVERY_MAP,EVERY_MEM,MEM_REVERSE]>>
  metis_tac[nz_lit_mk_lit,parse_vb_ilits_nz,MEM]
QED

Theorem parse_xlrupb_one_wf:
  parse_xlrupb_one lines = SOME (SOME (step,rest)) ⇒
  wf_xlrup step
Proof
  rw[parse_xlrupb_one_def,parse_xlrupb_rest_def]>>
  gvs[AllCaseEqs(),wf_xlrup_def]>>
  drule parse_xlrupb_chunk_wf>>
  simp[]
QED

Theorem parse_xlrupsb_wf:
  ∀lines xlrups.
  parse_xlrupsb lines = SOME xlrups ⇒
  EVERY wf_xlrup xlrups
Proof
  ho_match_mp_tac parse_xlrupsb_ind>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once parse_xlrupsb_def]>>
  rw[AllCaseEqs()]>>
  gvs[]>>
  metis_tac[parse_xlrupb_one_wf]
QED
