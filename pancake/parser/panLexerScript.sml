(**
 * The beginnings of a lexer for the Pancake language.
 *
 * We take significant inspiration from the Spark ADA development.
 *
 * Author: Craig McLaughlin
 * Date: March--April 2022
 *)
open HolKernel Parse boolLib bossLib stringLib numLib;

open arithmeticTheory stringTheory intLib listTheory locationTheory;
open ASCIInumbersTheory ASCIInumbersLib;

val _ = new_theory "panLexer";

Datatype:
  keyword = SkipK | StoreK | StoreBK | IfK | ElseK | WhileK
  | BrK | ContK | RaiseK | RetK | TicK | VarK | WithK | HandleK
  | LdsK | LdbK | BaseK | InK
End

Datatype:
  token = AndT | OrT | XorT | NotT
  | EqT | NeqT | LessT | GreaterT | GeqT
  | PlusT | MinusT | HashT | DotT | StarT
  | LslT | LsrT | AsrT | RorT
  | TrueT | FalseT | IntT int | IdentT string
  | LParT | RParT | CommaT | SemiT | ColonT | DArrowT | AddrT
  | LBrakT | RBrakT | LCurT | RCurT
  | AssignT
  | KeywordT keyword
  | LexErrorT
End

Datatype:
  atom = NumberA int | WordA string | SymA string | ErrA
End

Definition isAtom_singleton_def:
  isAtom_singleton c = MEM c "!+-&^|*().,;:[]{}"
End

Definition isAtom_begin_group_def:
  isAtom_begin_group c = MEM c "#=>"
End

Definition isAtom_in_group_def:
  isAtom_in_group c = MEM c "=<>"
End

Definition isAlphaNumOrWild_def:
  isAlphaNumOrWild c ⇔ isAlphaNum c ∨ c = #"_"
End

Definition get_token_def:
  get_token s =
  if s = "&" then AndT else
  if s = "|" then OrT else
  if s = "^" then XorT else
  if s = "==" then EqT else
  if s = "<>" then NeqT else
  if s = "<" then LessT else
  if s = ">" then GreaterT else
  if s = ">=" then GeqT else
  if s = "=>" then DArrowT else
  if s = "!" then NotT else
  if s = "+" then PlusT else
  if s = "-" then MinusT else
  if s = "*" then StarT else
  if s = "#" then HashT else
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
  LexErrorT
End

Definition get_keyword_def:
  get_keyword s =
  if s = "skip" then (KeywordT SkipK) else
  if s = "str" then (KeywordT StoreK) else
  if s = "strb" then (KeywordT StoreBK) else
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
  if s = "ldb" then (KeywordT LdbK) else
  if s = "@base" then (KeywordT BaseK) else
  if s = "true" then TrueT else
  if s = "false" then FalseT else
  if isPREFIX "@" s ∨ s = "" then LexErrorT else
  IdentT s
End

Definition token_of_atom_def:
  token_of_atom a =
  case a of
  | NumberA i => IntT i
  | WordA s => get_keyword s
  | SymA s => get_token s
  | ErrA => LexErrorT
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

Definition skip_comment_def:
  skip_comment "" _ = NONE ∧
  skip_comment (x::xs) loc =
  (case x of
   | #"\n" => SOME (xs, loc with col := loc.col + 1)
   | _ => skip_comment xs (loc with col := loc.col + 1))
End

Theorem skip_comment_thm:
  ∀xs l l' str. (skip_comment xs l = SOME (str, l')) ⇒
                              LENGTH str < LENGTH xs
Proof
  Induct
  >> fs[skip_comment_def]
  >> rw[]
  >> sg ‘STRLEN str < STRLEN xs’
  >- metis_tac[]
  >> fs[LE]
QED

Definition next_loc_def:
  next_loc n (POSN r c) = POSN r (c+n) ∧
  next_loc n x = x
End

Definition next_line_def:
  next_line (POSN r c) = POSN (r+1) 0 ∧
  next_line x = x
End

Definition low_row_def:
  loc_row n = POSN n 1
End

Definition next_atom_def:
  next_atom "" _ = NONE ∧
  next_atom (c::cs) loc =
    if c = #"\n" then (* Skip Newline *)
      next_atom cs (loc_row (loc.row + 1))
    else if isSpace c then
      next_atom cs (loc with col := loc.col + 1)
    else if isDigit c then
      let (n, cs') = read_while isDigit cs [c] in
        SOME (NumberA &(toNum n),
              Locs loc (loc with col := loc.col + LENGTH n),
              cs')
    else if c = #"-" ∧ cs ≠ "" ∧ isDigit (HD cs) then
      let (n, rest) = read_while isDigit cs [] in
      SOME (NumberA (0 - &(toNum n)),
            Locs loc (loc with col := loc.col + LENGTH n),
            rest)
    else if isPREFIX "//" (c::cs) then (* comment *)
      (case (skip_comment (TL cs) (loc with col := loc.col + 2)) of
       | NONE => SOME (ErrA, Locs loc (loc with col := loc.col + 2), "")
       | SOME (rest, loc') => next_atom rest loc')
    else if isAtom_singleton c then
      SOME (SymA (STRING c []), Locs loc loc, cs)
    else if isAtom_begin_group c then
      let (n, rest) = read_while isAtom_in_group cs [c] in
      SOME (SymA n, Locs loc (loc with col := loc.col + LENGTH n - 1), rest)
    else if isAlpha c ∨ c = #"@" then (* read identifier *)
      let (n, rest) = read_while isAlphaNumOrWild cs [c] in
      SOME (WordA n, Locs loc (loc with col := loc.col + LENGTH n), rest)
    else (* input not recognised *)
      SOME (ErrA, Locs loc loc, cs)
Termination
  WF_REL_TAC ‘measure (LENGTH o FST)’
  >> REPEAT STRIP_TAC
  >> fs[skip_comment_thm]
  >> Cases_on ‘cs’ >> fs[]
  >> sg ‘STRLEN p_1 < STRLEN t’
  >- metis_tac[skip_comment_thm]
  >> fs[LESS_EQ_IFF_LESS_SUC, LE]
End

Theorem next_atom_LESS:
  ∀input l s l' rest.
    next_atom input l = SOME (s, l', rest) ⇒ LENGTH rest < LENGTH input
Proof
  recInduct next_atom_ind >> rw[next_atom_def]
  >- metis_tac[DECIDE “x < y ⇒ x < SUC y”]
  >- metis_tac[DECIDE “x < y ⇒ x < SUC y”]
  >- (pairarg_tac >> drule read_while_thm >> gvs[])
  >- (pairarg_tac >> drule read_while_thm >> gvs[])
  >- (gvs[CaseEqs ["option", "prod", "list"]]
      >> drule_then assume_tac skip_comment_thm
      >> sg ‘STRLEN rest < STRLEN (TL cs)’ >> rw[]
      >> sg ‘STRLEN (TL cs) < SUC (STRLEN cs)’ >> rw[LENGTH_TL]
      >> Cases_on ‘cs’ >> simp[])
  >- (pairarg_tac >> drule read_while_thm >> gvs[])
  >- (pairarg_tac >> drule read_while_thm >> gvs[])
  >- (pairarg_tac >> drule read_while_thm >> gvs[])
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
      (token, Locs locB locE) :: pancake_lex_aux rest (locE with col := locE.col + 1))
Termination
  WF_REL_TAC ‘measure (LENGTH o FST)’ >> rw[]
  >> imp_res_tac next_token_LESS
End

Definition pancake_lex_def:
  pancake_lex input = pancake_lex_aux input init_loc
End

(* Tests :
   EVAL “pancake_ex "x + 1 --Then check y\n && y - 2 <= -3 || !z”;
*)

val _ = export_theory();
