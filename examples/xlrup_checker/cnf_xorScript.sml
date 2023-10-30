(*
  Syntax and semantics of CNF-XOR
*)
open preamble miscTheory mlstringTheory mlintTheory;

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

val _ = new_theory "cnf_xor";

(*
  A variable is drawn from type 'a

  A literal is either Pos or Neg

  Clauses and XORs are both lists of literals

  A CNF-XOR formula is a pair of list of clauses and list of XORs

  An assignment is a map from 'a to T/F

  A clause is satisfied by an assignment iff at least one of its literals is assigned to true

  An XOR is satisfied by an assignment iff the parity under the assignment is odd

  A CNF-XOR formula is satisfied by an assignment iff all its clauses and XORs are satisfied *)

Datatype:
  lit = Pos 'a | Neg 'a
End

Type clause = ``:'a lit list``;
Type cmsxor = ``:'a lit list``;
Type fml = ``:'a clause list # 'a cmsxor list``;
Type assignment = ``:'a -> bool``;

Definition sat_lit_def:
  sat_lit (w:'a assignment) l ⇔
  (case l of Pos x => w x | Neg x => ¬w x)
End

Definition sat_clause_def:
  sat_clause w C ⇔
  (∃l. l ∈ set C ∧ sat_lit w l)
End

Definition of_bool_def:
  (of_bool T = (1:num)) ∧
  (of_bool F = 0)
End

Definition sat_cmsxor_def:
  sat_cmsxor w C =
    ODD (SUM (MAP (of_bool o sat_lit w) C))
End

Definition sat_fml_def:
  sat_fml w (f:'a fml) = (
    (∀C. C ∈ set (FST f) ⇒ sat_clause w C) ∧
    (∀C. C ∈ set (SND f) ⇒ sat_cmsxor w C)
  )
End

Definition sols_def:
  sols f = {w | sat_fml w f}
End

(* A straightforward parser *)

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

(* CNF-XOR parser where 'a = num *)

(* Parse a list of literals ending with 0
  Literals only use variables between 1 to maxvar (inclusive) *)
Definition parse_lits_aux_def:
  (parse_lits_aux maxvar [] (acc:num lit list) = NONE) ∧
  (parse_lits_aux maxvar [c] acc =
    if c = INR 0i then SOME (REVERSE acc) else NONE) ∧
  (parse_lits_aux maxvar (x::xs) acc =
    case x of
      INR l =>
      let n = Num (ABS l) in
      let v = if l > 0 then Pos n else Neg n in
      if n = 0 ∨ n > maxvar then NONE
      else parse_lits_aux maxvar xs (v::acc)
    | INL (_:mlstring) => NONE)
End

Definition parse_clause_def:
  parse_clause maxvar xs = parse_lits_aux maxvar xs []
End

Definition parse_xor_def:
  parse_xor maxvar xs =
  case xs of [] => NONE
  | (c::cs) =>
  if c = INL (strlit "x")
  then parse_lits_aux maxvar cs []
  else NONE
End

(* lines which are not comments don't start with a single "c" *)
Definition nocomment_line_def:
  (nocomment_line (INL c::cs) = (c ≠ strlit "c")) ∧
  (nocomment_line _ = T)
End

Definition parse_line_def:
  parse_line maxvar xs =
  case parse_clause maxvar xs of
    SOME c => SOME (INL c)
  | NONE =>
  case parse_xor maxvar xs of
    SOME x => SOME (INR x)
  | NONE => NONE
End

(* Produces the list of clauses and XORs in order they are read *)
Definition parse_body_def:
  (parse_body maxvar [] cacc xacc =
    SOME (REVERSE cacc, REVERSE xacc)) ∧
  (parse_body maxvar (s::ss) cacc xacc =
    case parse_line maxvar s of
      NONE => NONE
    | SOME cx =>
      case cx of
        INL c => parse_body maxvar ss (c::cacc) xacc
      | INR x => parse_body maxvar ss cacc (x::xacc)
  )
End

Definition parse_header_line_def:
  parse_header_line ls =
  case ls of
    [p; cnf; vars; numls] =>
    if p = INL (strlit "p") ∧ cnf = INL (strlit "cnf")
    then
      case (vars, numls)
      of
        (INR v,INR c) => if v ≥ 0 ∧ c ≥ 0 then SOME (Num v,Num c) else NONE
      | _ => NONE
    else NONE
  | _ => NONE
End

Definition parse_cnf_xor_toks_def:
  parse_cnf_xor_toks tokss =
  let nocomments = FILTER nocomment_line tokss in
  case nocomments of
    s::ss =>
    (case parse_header_line s of
    SOME (vars,ncx) =>
      (case parse_body vars ss [] [] of NONE => NONE
      | SOME (cacc,xacc) =>
       if LENGTH cacc + LENGTH xacc = ncx then
        SOME (vars,ncx,cacc,xacc)
        else NONE)
    | NONE => NONE)
  | [] => NONE
End

Definition parse_cnf_xor_def:
  parse_cnf_xor strs =
  let tokss = MAP toks strs in
  case parse_cnf_xor_toks tokss of
    NONE => NONE
  | SOME (nvars, nclauses, ls) => SOME ls
End

val cnf_xor_raw = ``[
  strlit "c this is a comment";
  strlit "p cnf 5 8 ";
  strlit "    1  4 0";
  strlit "x   1  -5 0";
  strlit "c this is a comment";
  strlit "    2  4 0";
  strlit "    2  5 0";
  strlit "x  -3  4 0";
  strlit "    3  5 0";
  strlit "-1 -2 -3 0";
  strlit "c this is a comment";
  strlit "   -4 -5 0";
  ]``;

val test = rconc (EVAL ``THE (parse_cnf_xor ^(cnf_xor_raw))``);

val _ = export_theory ();
