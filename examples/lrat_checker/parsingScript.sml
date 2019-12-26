(*
   Parsing interface for DIMACS and LRAT
*)
open preamble miscTheory lratTheory mlintTheory;

val _ = new_theory "parsing";

(*
  Parses a list of strings (1 per line of a file) in DIMACS format
*)

val blanks_def = Define`
  blanks (c:char) ⇔ c = #" " ∨ c = #"\n" ∨ c = #"\t"`

(*
  A clause line must end with 0,
  cannot contain 0s elsewhere, and is within the var bound
  NOTE: the list can be sorted afterwards rather than doing insertions all the way.
  Hopefully not much difference if clauses are usually short...
*)
val parse_clause_def = Define`
  (parse_clause maxvar [] (acc:cclause) = NONE) ∧
  (parse_clause maxvar [c] acc =
    if c = (strlit "0") then SOME acc
    else NONE) ∧
  (parse_clause maxvar (x::xs) acc =
    case mlint$fromString x of
      NONE => NONE
    | SOME l =>
    if l = 0 ∨ l > &maxvar ∨ l < -&maxvar then NONE
    else parse_clause maxvar xs (l::acc)
  )`

Theorem parse_clause_MEM:
  ∀mv ls acc acc'.
  ¬MEM 0 acc ∧
  parse_clause mv ls acc = SOME acc' ⇒
  ¬MEM 0 acc'
Proof
  ho_match_mp_tac (fetch "-" "parse_clause_ind")>>
  rw[parse_clause_def]>>fs[]>>
  every_case_tac>>fs[]
QED

val parse_header_line_def = Define`
  parse_header_line str =
  let ls = tokens blanks str in
  case ls of
    [p; cnf; vars; numcls] =>
    if p = strlit "p" ∧ cnf = strlit "cnf"
    then
      case (mlint$fromNatString vars, mlint$fromNatString numcls)
      of
        (SOME v,SOME c) => SOME (v,c)
      | _ => NONE
    else NONE
  | _ => NONE`

(*
val res = EVAL ``parse_header_line (strlit"p cnf 1 2")``
*)

(*
  parse a strings as DIMACS
*)
val build_fml_def = Define`
  (build_fml maxvar (id:num) [] (acc:ccnf) = SOME acc) ∧
  (build_fml maxvar id (s::ss) acc =
    case parse_clause maxvar s [] of
    NONE => NONE
  | SOME cl => build_fml maxvar (id+1) ss (insert id cl acc))`

val parse_dimacs_def = Define`
  parse_dimacs strs =
  case strs of
    s::ss =>
      (case parse_header_line s of
      SOME (vars,clauses) =>
        let tokss = MAP (tokens blanks) ss in
        let nocomments = FILTER (λs. case s of x::xs => x ≠ strlit "c" | [] => T) tokss in
        if LENGTH nocomments = clauses then
          build_fml vars 1 nocomments LN
        else NONE
      | NONE => NONE)
  | [] => NONE`

Theorem build_fml_wf_fml:
  ∀ls mv id acc acc'.
  wf_fml acc ∧ build_fml mv id ls acc = SOME acc' ⇒
  wf_fml acc'
Proof
  Induct>>rw[build_fml_def]>>fs[]>>
  every_case_tac>>fs[]>>
  imp_res_tac parse_clause_MEM>>fs[]>>
  metis_tac[wf_fml_insert,parse_clause_MEM,wf_clause_def]
QED

Theorem parse_dimacs_wf:
  parse_dimacs strs = SOME fml ⇒
  wf_fml fml
Proof
  rw[parse_dimacs_def]>>
  every_case_tac>>fs[]>>
  match_mp_tac build_fml_wf_fml>>
  qmatch_asmsub_abbrev_tac`build_fml a b c d`>>
  qexists_tac`c`>>
  qexists_tac`a`>>
  qexists_tac`b`>>
  qexists_tac`d`>>
  unabbrev_all_tac>>fs[wf_fml_def,values_def,lookup_def]
QED

(* Parse a LRAT clause with witness *)

(* Gets the rest of the witness *)
val parse_until_zero_def = Define`
  (parse_until_zero [] acc = NONE) ∧
  (parse_until_zero (x::xs) acc =
    case mlint$fromString x of
      NONE => NONE
    | SOME l =>
    if l = 0:int then
      SOME (REVERSE acc, xs)
    else
      parse_until_zero xs (l::acc)
  )`

val parse_until_k_def = Define`
  (parse_until_k k [] acc = NONE) ∧
  (parse_until_k k (x::xs) acc =
    case mlint$fromString x of
      NONE => NONE
    | SOME l =>
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
    case mlint$fromString x of
      NONE => NONE
    | SOME l =>
    if l = 0:int then
      SOME ([], NONE , xs)
    else
      parse_until_k l xs [l])`


(* Parse everything until the next non-positive and returns it *)
val parse_until_nn_def = Define`
  (parse_until_nn [] acc = NONE) ∧
  (parse_until_nn (x::xs) acc =
    case mlint$fromString x of
      NONE => NONE
    | SOME l =>
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

val lit_from_int_def = Define`
  lit_from_int l =
  if l ≥ 0 then INL (Num l)
  else INR (Num (-l))`

(* LRAT parser *)
val parse_lratstep_def = Define`
  (parse_lratstep (cid::first::rest) =
  if first = strlit "d" then
    (* deletion line *)
    (case parse_until_nn rest [] of
       SOME (n, ls, []) => if n = 0 then SOME (Delete ls) else NONE
      | _ => NONE)
  else
  case mlint$fromNatString cid of
    NONE => NONE
  | SOME cid =>
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
            SOME (PR cid clause witness hint sp)
  ) ∧
  (parse_lratstep _ = NONE)`

(* Mostly semantic!*)
val parse_lrat_def = Define`
  (parse_lrat [] = SOME []) ∧
  (parse_lrat (l::ls) =
    case parse_lratstep (tokens blanks l) of
      NONE => NONE
    | SOME step =>
      (case parse_lrat ls of
        NONE => NONE
      | SOME ss => SOME (step :: ss))
    )`

val max_lit_def = Define`
  (max_lit k [] = k) ∧
  (max_lit k (x::xs) = if ABS x > k then max_lit (ABS x) xs else max_lit k xs)`

(*
val toString_def = Define`
  toString i =
    if 0i ≤ i ∧ i < 10 then
      str (toChar (Num (ABS i)))
    else
      implode ((if i < 0i then "-" else "")++
               (toChars (Num (ABS i) MOD maxSmall_DEC) (Num (ABS i) DIV maxSmall_DEC) ""))`;
*)

val print_line_def = Define`
  (print_line [] = strlit "0\n") ∧
  (print_line (x::xs) =
    mlint$toString x ^ strlit(" ") ^ print_line xs)`

(* print a formula out to DIMACS *)
val print_dimacs_def = Define`
  print_dimacs fml =
  let ls = MAP SND (toSortedAList fml) in
  let len = LENGTH ls in
  let v = max_lit 0 (MAP (max_lit 0) ls) in
  (strlit ("p cnf ") ^  mlint$toString v ^ strlit(" ") ^  mlint$toString (&len) ^ strlit("\n"))::
  MAP print_line ls`

(* TODO: this would be good to know
Theorem parse_of_print:
  parse_dimacs (print_dimacs fml) = SOME fml
Proof
  cheat
QED
 *)

val dimacsraw = ``[
  strlit "p cnf 5 8 ";
  strlit "    1  4 0";
  strlit "    1  5 0";
  strlit "    2  4 0";
  strlit "    2  5 0";
  strlit "    3  4 0";
  strlit "    3  5 0";
  strlit "-1 -2 -3 0";
  strlit "   -4 -5 0";
  ]``;

val cnf = rconc (EVAL ``THE (parse_dimacs ^(dimacsraw))``);

val back = rconc (EVAL``print_dimacs ^cnf``);

val lratraw = ``[
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

val lrat = rconc (EVAL ``THE (parse_lrat ^(lratraw))``);

val check = rconc (EVAL``THE (check_lrat ^(lrat) ^(cnf))``);

val _ = export_theory ();
