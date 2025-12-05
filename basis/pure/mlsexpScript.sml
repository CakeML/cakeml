(*
  Definition of a simple mlstring-based s-expression, incldues
  parsing and pretty printing for these s-expressions.
*)
Theory mlsexp
Ancestors
  mlstring
Libs
  preamble

(*--------------------------------------------------------------*
   Definition of s-expression
 *--------------------------------------------------------------*)

Datatype:
  sexp = Atom mlstring | Expr (sexp list)
End

(*--------------------------------------------------------------*
   Lexing + parsing
 *--------------------------------------------------------------*)

Datatype:
  token = OPEN | CLOSE | SYMBOL mlstring
End

Definition read_quoted_aux_def:
  read_quoted_aux [] acc = NONE ∧
  read_quoted_aux (#"\""::rest) acc =
    SOME (implode (REVERSE acc), rest) ∧
  read_quoted_aux (#"\\"::#"\""::rest) acc =
    read_quoted_aux rest (#"\""::acc) ∧
  read_quoted_aux (#"\\"::#"\\"::rest) acc =
    read_quoted_aux rest (#"\\"::acc) ∧
  read_quoted_aux (c::cs) acc =
    read_quoted_aux cs (c::acc)
End

(* Returns the string until a closing quote, and the rest of the input.
   Fails if closing quotes are missing. *)
Definition read_quoted_def:
  read_quoted (input: string) : (mlstring # string) option =
    read_quoted_aux input []
End

Theorem read_quoted_aux_length:
  ∀input acc.
    read_quoted_aux input acc = SOME (s, rest) ⇒ LENGTH rest ≤ LENGTH input
Proof
  ho_match_mp_tac read_quoted_aux_ind \\ rw[]
  \\ pop_assum mp_tac
  \\ once_rewrite_tac[read_quoted_aux_def]
  \\ EVERY_CASE_TAC
  \\ rpt strip_tac \\ res_tac \\ gvs[]
QED

Theorem read_quoted_length:
  read_quoted input = SOME (s, rest) ⇒ LENGTH rest ≤ LENGTH input
Proof
  rw[read_quoted_def] \\ imp_res_tac read_quoted_aux_length
QED

Definition read_atom_aux_def:
  read_atom_aux [] acc =
    (implode (REVERSE acc), []) ∧
  read_atom_aux (c::cs) acc =
    if MEM c ") \t\n" then (implode (REVERSE acc), (c::cs))
    else read_atom_aux cs (c::acc)
End

(* Returns the string until a closing parenthesis or whitespace, and the
   rest of the input. *)
Definition read_atom_def:
  read_atom (input: string) : (mlstring # string) =
    read_atom_aux input []
End

Theorem read_atom_aux_length:
  ∀input acc.
    read_atom_aux input acc = (s, rest) ⇒ LENGTH rest ≤ LENGTH input
Proof
  Induct
  \\ simp[read_atom_aux_def]
  \\ rw[read_atom_aux_def] \\ res_tac \\ gvs[]
QED

(* Where possible, we return our progress, and the rest of the input.
   INL and INR indicate failure and success, respectively. *)
Type result[local,pp] = “:α + α”

(* By tracking the depth, we can ensure we only lex one S-expression at a
   time. *)
Definition lex_aux_def:
  lex_aux depth [] acc : (token list # string) result =
    (if depth = 0:num then INR (acc, []) else INL (acc, [])) ∧
  lex_aux depth (c::cs) acc =
    if MEM c " \t\n" then lex_aux depth cs acc
    else if c = #"(" then lex_aux (depth + 1) cs (OPEN::acc)
    else if c = #")" then
      (if depth = 0 then INL (ARB, c::cs)
       else if depth = 1 then INR (CLOSE::acc, cs)
       else lex_aux (depth - 1) cs (CLOSE::acc))
    else if c = #"\"" then
      case read_quoted cs of
      | NONE => INL (acc, c::cs)
      | SOME (s, rest) =>
          if depth = 0 then INR ([SYMBOL s], rest)
          else lex_aux depth rest ((SYMBOL s)::acc)
    else
      case read_atom (c::cs) of
      | (s, rest) =>
          if depth = 0 then INR ([SYMBOL s], rest)
          else lex_aux depth rest ((SYMBOL s)::acc)
Termination
  wf_rel_tac ‘measure $ (λ(_, input, _). LENGTH input)’ \\ rw[]
  \\ imp_res_tac read_quoted_length \\ fs[]
  \\ fs[read_atom_def]
  \\ fs[Once read_atom_aux_def]
  \\ gvs [AllCaseEqs()]
  \\ imp_res_tac read_atom_aux_length \\ fs[]
End

(* Tokenizes (at most) one S-expression, and returns the rest of the input. *)
Definition lex_def:
  lex (input: string) : (token list # string) result =
    lex_aux 0 input []
End

Theorem test_lex[local]:
  lex " 1 2   3 " = INR ([SYMBOL «1»]," 2   3 ") ∧
  lex " (1 2) 3 " = INR ([CLOSE; SYMBOL «2»; SYMBOL «1»; OPEN]," 3 ") ∧
  lex " (1 2) ) " = INR ([CLOSE; SYMBOL «2»; SYMBOL «1»; OPEN]," ) ") ∧
  lex " ) (1 2) " = INL (ARB,") (1 2) ")
Proof
  EVAL_TAC
QED

(* TODO Something feels off about this... are we correctly dealing with
   failures? *)
Definition parse_aux_def:
  parse_aux [] xs s = xs ∧
  parse_aux (CLOSE :: rest) xs s = parse_aux rest [] (xs::s) ∧
  parse_aux (OPEN :: rest) xs s =
    (case s of
     | [] => parse_aux rest xs s
     | (y::ys) => parse_aux rest ((Expr xs)::y) ys) ∧
  parse_aux ((SYMBOL sy) :: rest) xs s = parse_aux rest ((Atom sy)::xs) s
End

Definition parse_def:
  parse input =
    case lex input of
    | INL (err, rest) => INL (err, rest)
    | INR (rev_toks, rest) => INR (parse_aux rev_toks [] [], rest)
End

Theorem test_parse[local]:
  parse " 1 2 3 " = INR ([Atom «1»]," 2 3 ") ∧
  parse "(1 2 3)" = INR ([Expr [Atom «1»; Atom «2»; Atom «3»]],"") ∧
  parse "(()) ()" = INR ([Expr [Expr []]]," ()")
Proof
  EVAL_TAC
QED
