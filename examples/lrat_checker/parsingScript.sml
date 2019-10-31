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

(* A clause line must end with 0,
  cannot contain 0s elsewhere, and is within the var bound *)
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
    else parse_clause maxvar xs (insert_literal (Num (ABS l)) (l ≥ (0:int)) acc)
  )`

(* A single line of file as a string *)
(* val parse_dimacs_line_def = Define`
  (parse_dimacs_line maxvar str =
  (* For now, split the line into space separated string*)
  let ls = tokens blanks str in parse_clause maxvar ls [])` *)

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
  Mostly semantic!
*)
val build_fml_def = Define`
  (build_fml maxvar (id:num) [] (acc:ccnf) = SOME acc) ∧
  (build_fml maxvar id (s::ss) acc =
    case parse_clause maxvar s (LN,LN) of
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

(* Parse everything until the next zero and returns it *)
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

val parse_RAT_hint_def = tDefine "parse_RAT_hint" `
  parse_RAT_hint id xs acc =
  if id = 0 then
    if xs = [] then SOME acc
    else NONE
  else
  case parse_until_nn xs [] of
    NONE => NONE
  | SOME (n,clause,rest) =>
      parse_RAT_hint n rest (insert id clause acc)`
  (WF_REL_TAC `measure (LENGTH o (FST o SND))`>>
  rw[]>>
  drule parse_until_nn_length>>fs[])

val lit_from_int_def = Define`
  lit_from_int l =
  if l ≥ 0 then INL (Num l)
  else INR (Num (-l))`

val cclause_from_list_def = Define`
  cclause_from_list ls =
  FOLDR (λl acc. (insert_literal (Num (ABS l)) (l ≥ (0:int)) acc)) (LN,LN) ls`

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
    (* RAT line *)
    case parse_until_zero (first::rest) [] of
      NONE => NONE
    | SOME (clause,rest) =>
      case parse_until_nn rest [] of
        NONE => NONE
      | SOME (id,hint,rest) =>
        case parse_RAT_hint id rest LN of
          NONE => NONE
        | SOME sp =>
          case clause of
            [] => SOME (RAT cid (INL 0) (cclause_from_list clause) hint sp)
          | _ => SOME (RAT cid (lit_from_int (HD clause)) (cclause_from_list clause) hint sp)
  ) ∧
  (parse_lratstep _ = NONE)`

(* Mostly semantic! *)
val parse_lrat_aux_def = Define`
  (parse_lrat_aux [] acc = SOME (REVERSE acc)) ∧
  (parse_lrat_aux (l::ls) acc =
    case parse_lratstep (tokens blanks l) of
      NONE => NONE
    | SOME step => parse_lrat_aux ls (step::acc)
    )`

val parse_lrat_def = Define`
  parse_lrat ls = parse_lrat_aux ls []`

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
