(*
  Definitions to lex and parse S-expressions.
*)
Theory mlsexp
Ancestors
  mlstring
Libs
  preamble

Datatype:
  token = OPEN | CLOSE | SYMBOL mlstring
End

Datatype:
  sexp = Atom mlstring | Expr (sexp list)
End

Definition read_quoted_aux_def:
  read_quoted_aux [] acc = NONE ∧
  read_quoted_aux (#"\""::rest) acc =
    SOME ((REVERSE acc), rest) ∧
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
  read_quoted (input: string) : (string # string) option =
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
    ((REVERSE acc), []) ∧
  read_atom_aux (c::cs) acc =
    if MEM c ") \t\n" then ((REVERSE acc), (c::cs))
    else read_atom_aux cs (c::acc)
End

(* Returns the string until a closing parenthesis or whitespace, and the
   rest of the input. *)
Definition read_atom_def:
  read_atom (input: string) : (string # string) =
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
    (if depth = 0 then INR (acc, []) else INL (acc, [])) ∧
  lex_aux depth (c::cs) acc =
    if MEM c " \t\n" then lex_aux depth cs acc
    else if c = #"(" then lex_aux (depth + 1) cs (OPEN::acc)
    else if c = #")" then
      (if 0 < depth
       then lex_aux (depth - 1) cs (CLOSE::acc)
       else INL (acc, c::cs))
    else if c = #"\"" then
      case read_quoted cs of
      | NONE => INL (acc, c::cs)
      | SOME (s, rest) =>
          lex_aux depth rest ((SYMBOL (implode s))::acc)
    else
      case read_atom (c::cs) of
      | (s, rest) =>
          lex_aux depth rest ((SYMBOL (implode s))::acc)
Termination
  wf_rel_tac ‘measure $ (λx. case x of (_, input, _) => LENGTH input)’ \\ rw[]
  \\ imp_res_tac read_quoted_length \\ fs[]
  \\ pop_assum mp_tac
  \\ simp[read_atom_def]
  \\ simp[Once read_atom_aux_def]
  \\ strip_tac
  \\ imp_res_tac read_atom_aux_length \\ fs[]
End

(* Tokenizes (at most) one S-expression, and returns the rest of the input. *)
Definition lex_def:
  lex (input: string) : (token list # string) result =
    lex_aux 0 input []
End

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
