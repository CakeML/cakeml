(*
 * Definitions to lex and parse S-expressions.
 *)

open preamble
open result_monadTheory

val _ = new_theory "dafny_sexp";

(* FIXME Properly escape characters
 *
 * Unsure whether we correctly deal with the escaping behavior from the string
 * generated by Dafny. *)

(* TODO Address character set support
 * 
 * Dafny supports richer character sets; unclear how that is/should be handled. *)
     
(* Lexing *)
Datatype:
  token = OPEN | CLOSE | STRTOK string
End

Definition read_quoted_aux_def:
  read_quoted_aux [] acc =
    fail "read_quoted_aux: Missing closing quotes" ∧
  read_quoted_aux (#"\""::rest) acc =
    return ((REVERSE acc), rest) ∧
  read_quoted_aux (#"\\"::#"\""::rest) acc =
    read_quoted_aux rest (#"\""::acc) ∧
  read_quoted_aux (c::cs) acc =
    read_quoted_aux cs (c::acc)
End
Definition read_quoted_def:
  read_quoted (cs: string) =
    read_quoted_aux cs []
End

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

Definition lex_aux_def:
  lex_aux [] acc =
    return acc ∧
  lex_aux (c::cs) acc =
    if MEM c " \t\n" then lex_aux cs acc
    else if c = #"(" then lex_aux cs (OPEN::acc)
    else if c = #")" then lex_aux cs (CLOSE::acc)
    else if c = #"\"" then
      do
        (s, rest) <- read_quoted cs;
        lex_aux rest ((STRTOK s)::acc)
      od
    else
      case read_atom (c::cs) of
      | (s, rest) =>
          lex_aux rest ((STRTOK s)::acc)
Termination
  cheat
End
Definition lex_def:
  lex cs =
    lex_aux cs []
End

(* Parsing *)
Datatype:
  sexp = Atom string | Expr (sexp list)
End

Definition parse_aux_def:
  parse_aux ((STRTOK s)::rest) acc =
    parse_aux rest ((Atom s)::acc) ∧
  parse_aux (CLOSE::rest) acc =
    do
      (e, rest) <- (parse_aux rest []);
      parse_aux rest (e::acc)
    od ∧
  parse_aux (OPEN::rest) acc =  (* Need to consume OPEN *)
    return (Expr (acc), rest) ∧
  parse_aux [] acc =
    return (Expr (acc), [])
Termination
  cheat
End

Definition parse_def:
  parse [(STRTOK s)] =
    return (Atom s) ∧
  parse (CLOSE::rest) =
    do
      (e, rest) <- (parse_aux rest []);
      if rest = [] then
        return e
      else fail ("parse: Tokens still remaining after parsing Expr")
    od ∧
  parse ts =
    fail ("parse: First token was not STRTOK or CLOSE")
End

(* TODO move this away *)

(* Testing *)
(* open TextIO *)
(* val inStream = TextIO.openIn "./test.sexpr"; *)
(* val fileContent = TextIO.inputAll inStream; *)
(* val _ = TextIO.closeIn inStream; *)
(* val fileContent_tm = stringSyntax.fromMLstring fileContent; *)


(* val lex_r = rhs (concl(EVAL “lex ^fileContent_tm”)); *)
(* val parse_r = rhs (concl (EVAL “parse (OUTL (^lex_r))”)); *)

val _ = export_theory ();
