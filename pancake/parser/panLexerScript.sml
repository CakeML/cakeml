(**
 * A lexer for the Pancake language.
 *)

(**
 * We take significant inspiration from the Spark ADA development.
 *
 * Author: Craig McLaughlin
 * Date: March--April 2022
 *)

open HolKernel Parse boolLib bossLib stringLib numLib;

open arithmeticTheory stringTheory intLib listTheory locationTheory;
open ASCIInumbersTheory ASCIInumbersLib;
open mlstringTheory;

val _ = new_theory "panLexer";

Datatype:
  keyword = SkipK | StK | StwK | St8K | St32K | IfK | ElseK | WhileK
  | BrK | ContK | RaiseK | RetK | TicK | VarK | WithK | HandleK | BiwK
  | LdsK | Ld8K | LdwK | Ld32K | BaseK | InK | FunK | ExportK | TrueK | FalseK
End

Datatype:
  token = AndT | OrT | BoolAndT | BoolOrT | XorT | NotT
  | EqT | NeqT | LessT | GreaterT | GeqT | LeqT | LowerT | HigherT | HigheqT | LoweqT
  | PlusT | MinusT | DotT | StarT
  | LslT | LsrT | AsrT | RorT
  | IntT int | IdentT string | ForeignIdent string (* @ffi_str except @base *)
  | LParT | RParT | CommaT | SemiT | ColonT | DArrowT | AddrT
  | LBrakT | RBrakT | LCurT | RCurT
  | AssignT
  | StaticT
  | KeywordT keyword
  | AnnotCommentT string
  | LexErrorT mlstring
End

Datatype:
  atom = NumberA int | WordA string | SymA string | ErrA mlstring | AnnotCommentA string
End

Definition isAtom_singleton_def:
  isAtom_singleton c = MEM c "+-^*().,;:[]{}"
End

Definition isAtom_begin_group_def:
  (* # is for only for RorT,
  * and should remove it to avoid collision with
  * C-preprocessor later *)
  isAtom_begin_group c = MEM c "#=><!&|"
End

Definition isAtom_in_group_def:
  isAtom_in_group c = MEM c "=<>|&+"
End

Definition isAlphaNumOrWild_def:
  isAlphaNumOrWild c ⇔ isAlphaNum c ∨ c = #"_"
End

Definition isLexErrorT_def:
  (isLexErrorT (LexErrorT _) ⇔ T) ∧
  (isLexErrorT _ ⇔ F)
End

Definition dest_lexErrorT_def:
  (destLexErrorT (LexErrorT msg) = SOME msg) ∧
  destLexErrorT _ = NONE
End

Definition get_token_def:
  get_token s =
  if s = "&&" then BoolAndT else
  if s = "||" then BoolOrT else
  if s = "&" then AndT else
  if s = "|" then OrT else
  if s = "^" then XorT else
  if s = "==" then EqT else
  if s = "!=" then NeqT else
  if s = "<" then LessT else
  if s = ">" then GreaterT else
  if s = ">=" then GeqT else
  if s = "<=" then LeqT else
  if s = "<+" then LowerT else
  if s = ">+" then HigherT else
  if s = ">=+" then HigheqT else
  if s = "<=+" then LoweqT else
  if s = "=>" then DArrowT else
  if s = "!" then NotT else
  if s = "+" then PlusT else
  if s = "-" then MinusT else
  if s = "*" then StarT else
  if s = "." then DotT else
  if s = "<<" then LslT else
  if s = ">>>" then LsrT else
  if s = ">>" then AsrT else
  if s = "#>>" then RorT else
  if s = "(" then LParT else
  if s = ")" then RParT else
  if s = "," then CommaT else
  if s = ";" then SemiT else
  if s = ":" then ColonT else
  if s = "[" then LBrakT else
  if s = "]" then RBrakT else
  if s = "{" then LCurT else
  if s = "}" then RCurT else
  if s = "=" then AssignT else
  LexErrorT $ concat [«Unrecognised symbolic token: »; implode s]
End

Definition get_keyword_def:
  get_keyword s =
  if s = "skip" then (KeywordT SkipK) else
  if s = "st" then (KeywordT StK) else
  if s = "stw" then (KeywordT StwK) else
  if s = "st8" then (KeywordT St8K) else
  if s = "st32" then (KeywordT St32K) else
  if s = "if" then (KeywordT IfK) else
  if s = "else" then (KeywordT ElseK) else
  if s = "while" then (KeywordT WhileK) else
  if s = "break" then (KeywordT BrK) else
  if s = "continue" then (KeywordT ContK) else
  if s = "raise" then (KeywordT RaiseK) else
  if s = "return" then (KeywordT RetK) else
  if s = "tick" then (KeywordT TicK) else
  if s = "var" then (KeywordT VarK) else
  if s = "in" then (KeywordT InK) else
  if s = "with" then (KeywordT WithK) else
  if s = "handle" then (KeywordT HandleK) else
  if s = "lds" then (KeywordT LdsK) else
  if s = "ldw" then (KeywordT LdwK) else
  if s = "ld8" then (KeywordT Ld8K) else
  if s = "ld32" then (KeywordT Ld32K) else
  if s = "@base" then (KeywordT BaseK) else
  if s = "@biw" then (KeywordT BiwK) else
  if s = "true" then (KeywordT TrueK) else
  if s = "false" then (KeywordT FalseK) else
  if s = "fun" then (KeywordT FunK) else
  if s = "export" then (KeywordT ExportK) else
  if s = "" then LexErrorT $ «Expected keyword, found empty string» else
  if 2 <= LENGTH s ∧ EL 0 s = #"@" then ForeignIdent (DROP 1 s)
  else
    IdentT s
End

Definition token_of_atom_def:
  token_of_atom a =
  case a of
  | NumberA i => IntT i
  | WordA s => get_keyword s
  | SymA s => get_token s
  | ErrA s => LexErrorT s
  | AnnotCommentA s => AnnotCommentT s
End

Definition read_while_def:
  (read_while P "" s = (IMPLODE (REVERSE s), "")) ∧
  (read_while P (STRING c cs) s =
   if P c then read_while P cs (c :: s)
   else (IMPLODE (REVERSE s), STRING c cs))
End

Theorem read_while_thm:
  ∀P input s s' rest.
     read_while P input s = (s', rest) ⇒ LENGTH rest ≤ LENGTH input
Proof
  Induct_on `input` >> rw[read_while_def] >> gvs[]
  >> metis_tac[DECIDE “x ≤ y ⇒ x ≤ SUC y”]
QED

Definition next_loc_def:
  next_loc n (POSN r c) = POSN r (c+n) ∧
  next_loc n x = x
End

Definition next_line_def:
  next_line (POSN r c) = POSN (r+1) 0 ∧
  next_line x = x
End

Definition loc_row_def:
  loc_row n = POSN n 1
End

Definition skip_comment_def:
  skip_comment "" _ _ = NONE ∧
  skip_comment (x::xs) loc i =
  (case x of
   | #"\n" => SOME (next_line loc, i + 1n)
   | _ => skip_comment xs (next_loc 1 loc) (i + 1n))
End

(* return SOME (loc, i, j) -> i characters in comment, DROP j characters to
   continue parsing (after the closing '*/') at loc *)
Definition skip_block_comment_def:
  skip_block_comment "" _ _ = NONE ∧
  skip_block_comment [_] _ _ = NONE ∧
  skip_block_comment (x::y::xs) loc i =
  if x = #"*" ∧ y = #"/" then
    SOME (next_loc 2 loc, i, i + 2)
  else if x = #"\n" then
    skip_block_comment (y::xs) (next_line loc) (i + 1n)
  else
    skip_block_comment (y::xs) (next_loc 1 loc) (i + 1n)
End

Definition unhex_alt_def:
  unhex_alt x = if isHexDigit x then UNHEX x else 0n
End

Definition num_from_dec_string_alt_def:
  num_from_dec_string_alt = s2n 10 unhex_alt
End

Definition next_atom_def:
  next_atom "" _ = NONE ∧
  next_atom (c::cs) loc =
    if c = #"\n" then (* Skip Newline *)
      next_atom cs (next_line loc)
    else if isSpace c then
      next_atom cs (next_loc 1 loc)
    else if isDigit c then
      let (n, cs') = read_while isDigit cs [c] in
        SOME (NumberA &(num_from_dec_string_alt n),
              Locs loc (next_loc (LENGTH n) loc),
              cs')
    else if c = #"-" ∧ cs ≠ "" ∧ isDigit (HD cs) then
      let (n, rest) = read_while isDigit cs [] in
      SOME (NumberA (0 - &(num_from_dec_string_alt n)),
            Locs loc (next_loc (LENGTH n) loc),
            rest)
    else if isPREFIX "//" (c::cs) then (* comment *)
      (case (skip_comment (TL cs) (next_loc 2 loc) 0n) of
       | NONE => SOME (ErrA «Malformed comment», Locs loc (next_loc 2 loc), "")
       | SOME (loc', len) => next_atom (DROP (len + 1) cs) loc')
    else if isPREFIX "/*@" (c::cs) then (* annotation block comment *)
      (case (skip_block_comment (TL cs) (next_loc 3 loc) 0n) of
       | NONE => SOME (ErrA «Malformed comment», Locs loc (next_loc 3 loc), "")
       | SOME (loc', i, len) => SOME (AnnotCommentA (TAKE i (TL cs)),
            Locs loc loc', DROP (len + 1) cs))
    else if isPREFIX "/*" (c::cs) then (* block comment *)
      (case (skip_block_comment (TL cs) (next_loc 2 loc) 0n) of
       | NONE => SOME (ErrA «Malformed comment», Locs loc (next_loc 2 loc), "")
       | SOME (loc', _, len) => next_atom (DROP (len + 1) cs) loc')
    else if isAtom_singleton c then
      SOME (SymA (STRING c []), Locs loc loc, cs)
    else if isAtom_begin_group c then
      let (n, rest) = read_while isAtom_in_group cs [c] in
      SOME (SymA n, Locs loc (next_loc (LENGTH n - 1) loc), rest)
    else if isAlpha c ∨ c = #"@" then (* read identifier *)
      let (n, rest) = read_while isAlphaNumOrWild cs [c] in
      SOME (WordA n, Locs loc (next_loc (LENGTH n) loc), rest)
    else (* input not recognised *)
      SOME (ErrA $ concat [«Unrecognised symbol: »; str c], Locs loc loc, cs)
Termination
  WF_REL_TAC `measure (LENGTH o FST)`
  \\ simp []
End

Theorem next_atom_LESS:
  ∀input l s l' rest.
    next_atom input l = SOME (s, l', rest) ⇒ LENGTH rest < LENGTH input
Proof
  recInduct next_atom_ind \\ simp [next_atom_def]
  \\ rw []
  \\ TRY (first_x_assum drule)
  \\ fs [miscTheory.UNCURRY_eq_pair, CaseEq "option", CaseEq "prod"]
  \\ gvs []
  \\ imp_res_tac read_while_thm
  \\ fs []
  \\ BasicProvers.EVERY_CASE_TAC \\ fs []
QED

Definition next_token_def:
  next_token input loc =
  case next_atom input loc of
   | NONE => NONE
   | SOME (atom, locs, rest) =>
       SOME (token_of_atom atom, locs, rest)
End

Theorem next_token_LESS:
  ∀s l l' rest input. (next_token input l = SOME (s, l', rest)) ⇒
                                  LENGTH rest < LENGTH input
Proof
  rw[next_token_def, AllCaseEqs()] >> metis_tac[next_atom_LESS]
QED

Definition init_loc_def:
  init_loc = POSN 1 1
End

Definition pancake_lex_aux_def:
 pancake_lex_aux input loc =
 (case next_token input loc of
  | NONE => []
  | SOME (token, Locs locB locE, rest) =>
      (token, Locs locB locE) :: pancake_lex_aux rest locE)
Termination
  WF_REL_TAC ‘measure (LENGTH o FST)’ >> rw[]
  >> imp_res_tac next_token_LESS
End

Definition pancake_lex_def:
  pancake_lex input = pancake_lex_aux input init_loc
End

Definition safe_pancake_lex_def:
  safe_pancake_lex input =
  (let output = pancake_lex input in
      case FILTER (isLexErrorT ∘ FST) output of
        [] => INL output
      | xs => INR $ MAP ((the «» ∘ destLexErrorT) ## I) xs)
End

(* Tests :
   EVAL ``pancake_lex "x + 1 --Then check y\n && y - 2 <= -3 || !z"``;
*)

val _ = export_theory();
