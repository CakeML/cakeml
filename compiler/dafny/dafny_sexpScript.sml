(*
  Definitions to lex and parse S-expressions.
*)
Theory dafny_sexp
Ancestors
  mlstring result_monad
Libs
  preamble


(* Datatypes *)

Datatype:
  token = OPEN | CLOSE | STRTOK mlstring
End

Datatype:
  sexp = Atom mlstring | Expr (sexp list)
End

(* Definition for lexing *)

Definition read_quoted_aux_def:
  read_quoted_aux [] acc =
    fail «read_quoted_aux: Missing closing quotes» ∧
  read_quoted_aux (#"\""::rest) acc =
    return ((REVERSE acc), rest) ∧
  read_quoted_aux (#"\\"::#"\""::rest) acc =
    read_quoted_aux rest (#"\""::acc) ∧
  read_quoted_aux (#"\\"::#"\\"::rest) acc =
    read_quoted_aux rest (#"\\"::acc) ∧
  read_quoted_aux (c::cs) acc =
    read_quoted_aux cs (c::acc)
End

Definition read_quoted_def:
  read_quoted (cs: string) =
    read_quoted_aux cs []
End

Theorem read_quoted_aux_length:
  ∀cs acc x y. read_quoted_aux cs acc = INR (x, y) ⇒ LENGTH y ≤ LENGTH cs
Proof
  ho_match_mp_tac read_quoted_aux_ind \\ rw[]
  \\ pop_assum mp_tac
  \\ once_rewrite_tac[read_quoted_aux_def]
  \\ EVERY_CASE_TAC
  \\ rpt strip_tac \\ res_tac \\ gvs[]
QED

Definition read_atom_aux_def:
  read_atom_aux [] acc =
    ((REVERSE acc), []) ∧
  read_atom_aux (c::cs) acc =
    if MEM c ") \t\n" then ((REVERSE acc), (c::cs))
    else read_atom_aux cs (c::acc)
End

Definition read_atom_def:
  read_atom cs =
    read_atom_aux cs []
End

Theorem read_atom_aux_length:
  ∀cs x y acc. read_atom_aux cs acc = (x, y) ⇒ LENGTH y ≤ LENGTH cs
Proof
  Induct
  \\ simp[read_atom_aux_def]
  \\ rw[read_atom_aux_def] \\ res_tac \\ gvs[]
QED

Theorem read_quoted_length:
  ∀cs x y. read_quoted cs = INR (x, y) ⇒ LENGTH y ≤ LENGTH cs
Proof
  rw[read_quoted_def] \\ imp_res_tac read_quoted_aux_length
QED

(* Adapted from
 * https://github.com/dafny-lang/dafny/blob/bc6b587e264e3c531c4d6698abd421abdff3aea9/Source/DafnyCore/Generic/Util.cs#L341
 *)
Definition unescape_string_def:
  unescape_string (c1::c2::rest) =
  (if c1 = #"\\" ∧ c2 = #"'" then
     #"'"::(unescape_string rest)
   else if c1 = #"\\" ∧ c2 = #"\"" then
     #"\""::(unescape_string rest)
   else if c1 = #"\\" ∧ c2 = #"\\" then
     #"\\"::(unescape_string rest)
   else if c1 = #"\\" ∧ c2 = #"0" then
     #"\000"::(unescape_string rest)
   else if c1 = #"\\" ∧ c2 = #"n" then
     #"\n"::(unescape_string rest)
   else if c1 = #"\\" ∧ c2 = #"r" then
     #"\r"::(unescape_string rest)
   else if c1 = #"\\" ∧ c2 = #"t" then
     #"\t"::(unescape_string rest)
   else
    c1::(unescape_string (c2::rest))) ∧
  unescape_string (c::rest) = (c::(unescape_string rest)) ∧
  unescape_string "" = ""
End

(* Removed use of monads for termination proof *)
Definition lex_aux_def:
  lex_aux [] acc =
    (INR acc) ∧
  lex_aux (c::cs) acc =
    if MEM c " \t\n" then lex_aux cs acc
    else if c = #"(" then lex_aux cs (OPEN::acc)
    else if c = #")" then lex_aux cs (CLOSE::acc)
    else if c = #"\"" then
      case read_quoted cs of
      | INL msg => INL msg
      | INR (s, rest) =>
          lex_aux rest ((STRTOK (implode (unescape_string s)))::acc)
    else
      case read_atom (c::cs) of
      | (s, rest) =>
          lex_aux rest ((STRTOK (implode (unescape_string s)))::acc)
Termination
  WF_REL_TAC ‘measure $ LENGTH o FST’ \\ rw[]
  \\ imp_res_tac read_quoted_length \\ fs[]
  \\ pop_assum mp_tac
  \\ simp[read_atom_def]
  \\ simp[Once read_atom_aux_def]
  \\ strip_tac
  \\ imp_res_tac read_atom_aux_length \\ fs[]
End

Definition lex_def:
  lex cs = lex_aux cs []
End

(* Definitions for parsing *)

Definition parse_aux_def:
  parse_aux [] xs s = xs ∧
  parse_aux (CLOSE :: rest) xs s = parse_aux rest [] (xs::s) ∧
  parse_aux (OPEN :: rest) xs s =
    (case s of
     | [] => parse_aux rest xs s
     | (y::ys) => parse_aux rest ((Expr xs)::y) ys) ∧
  parse_aux ((STRTOK st) :: rest) xs s = parse_aux rest ((Atom st)::xs) s
End

Definition parse_def:
  parse toks =
  case parse_aux toks [] [] of
  | [e] => return e
  | _ => fail «parse: Not exactly one S-expression in input»
End

