(*
  Lexer for the caml frontend.
 *)

open preamble locationTheory;

val _ = new_theory "caml_lex";

(* TODO
 * - Location spans might be wrong just about everywhere
 * - Maybe won't need so many different tokens for symbols
 *)

(* -------------------------------------------------------------------------
 * Tokens
 * ------------------------------------------------------------------------- *)

Datatype:
  reserved_word
    = AndR | AsR | AssertR | AsrR | BeginR | ClassR | ConstraintR | DoR | DoneR
    | DowntoR | ElseR | EndR | ExceptionR | ExternalR | FalseR | ForR | FunR
    | FunctionR | FunctorR | IfR | InR | IncludeR | InheritR | InitializerR
    | LandR | LazyR | LetR | LorR | LslR | LsrR | LxorR | MatchR | MethodR
    | ModR | ModuleR | MutableR | NewR | NonrecR | ObjectR | OfR | OpenR
    | OrR | PrivateR | RecR | SigR | StructR | ThenR | ToR | TrueR | TryR
    | TypeR | ValR | VirtualR | WhenR | WhileR | WithR
End

Datatype:
  reserved_symb
    = NeqRS | HashRS | AndbRS | AndRS | TickRS | LparRS | RparRS | MulRS
    | PlusRS | CommaRS | DashRS | DashdRS | RarrowRS | DotRS | DotsRS | DottRS
    | ColonRS | ColonsRS | RassignRS | SigsubRS | SemiRS | SemisRS | LessRS
    | LarrowRS | EqualRS | GreaterRS | QuestionRS | LbrackRS | RbrackRS | AnyRS
    | QtickRS | LbraceRS | RbraceRS | OrbRS | OrlRS | TildeRS
    (* missing: >], >}, [<, [>, [|, |], *)
End

Datatype:
  token
    = ReswT reserved_word       (* reserved word     *)
    | RessymT reserved_symb     (* reserved symbol   *)
    | PSymT string              (* prefix symbol     *)
    | ISymT string              (* infix symbol      *)
    | Hol_infixT string         (* THEN, THENC, etc. *)
    | IntT int                  (* integer literal   *)
    | CharT char                (* character literal *)
    | StrT string               (* string literal    *)
    | UIdentT string            (* [U]ppercase ident *)
    | LIdentT string            (* [l]owercase ident *)
    | UnknownT string           (* Bad token         *)
End

(* -------------------------------------------------------------------------
 * Pre-tokens
 * ------------------------------------------------------------------------- *)

Datatype:
  symbol
    = NumberS int
    | StringS string
    | CharS char
    | OtherS string
    | ErrorS
End

(* INTEGERS
 *
 *   int-lit ::= [-]? [0-9] [0-9_]*
 *             | [-]? ("0x"|"0X") [0-9a-fA-F] [0-9a-fA-F_]*
 *             | [-]? ("0o"|"0O") [0-7] [0-7_]*
 *             | [-]? ("0b"|"0B") [0-1] [0-1_]*
 *
 *   int32-lit ::= int-lit "l"
 *   int64-lit ::= int-lit "L"
 *   intn-lit  ::= int-lit "n"
 *)

Definition unhex_alt_def:
  unhex_alt x = if isHexDigit x then UNHEX x else 0n
End

Definition isOctDigit_def:
  isOctDigit c ⇔ 48 ≤ ORD c ∧ ORD c ≤ 55
End

Definition isBinDigit_def:
  isBinDigit c ⇔ 48 ≤ ORD c ∧ ORD c ≤ 49
End

Definition oct2num_def:
  oct2num = s2n 8 unhex_alt
End

Definition hex2num_def:
  hex2num = s2n 16 unhex_alt
End

Definition bin2num_def:
  bin2num = s2n 2 unhex_alt
End

Definition dec2num_def:
  dec2num = s2n 10 unhex_alt
End

Definition take_while_aux_def:
  take_while_aux acc p xs =
    case xs of
      [] => (REVERSE acc, xs)
    | x::xs =>
        if p x then take_while_aux (x::acc) p xs
        else (REVERSE acc, x::xs)
End

Definition take_while_def:
  take_while = take_while_aux []
End

Definition skip_comment_def:
  skip_comment cs d loc =
    case cs of
      x::y::xs =>
        if x = #"(" ∧ y = #"*" then
          skip_comment xs (d + 1) (loc with col := loc.col + 2)
        else if x = #"*" ∧ y = #")" then
          let loc' = loc with col := loc.col + 2 in
            if d = 0n then SOME (xs, loc') else skip_comment xs (d - 1) loc'
        else if x = #"\n" then
          skip_comment (y::xs) d (loc with <| col := 0; row := loc.row + 1 |>)
        else
          skip_comment (y::xs) d (loc with col := loc.col + 1)
    | _ => NONE
End

Theorem skip_comment_thm:
  ∀xs d loc.
    skip_comment xs d loc = SOME (ys, loc') ⇒
      LENGTH ys ≤ LENGTH xs
Proof
  ho_match_mp_tac skip_comment_ind \\ rw []
  \\ pop_assum mp_tac
  \\ simp [Once skip_comment_def]
  \\ rw [CaseEqs ["option", "string", "bool"]] \\ gs []
QED

(* ESCAPE SEQUENCE
 *
 *  esc-seq  ::= "\" [\\"'ntr\s]
 *             | "\" [0-9][0-9][0-9]
 *             | "\x" [0-9][0-9]
 *             | "\o" [0-3][0-7][0-7]
 *  char-lit ::= "'" (<char> | esc-seq) "'"
 *)

Definition scan_escseq_def:
  scan_escseq s loc =
    case s of
      #"\\" :: cs =>
        (case cs of
           #"\\" :: rest =>
             SOME (#"\\", rest, loc with col := loc.col + 2)
         | #"\"" :: rest =>
             SOME (#"\"", rest, loc with col := loc.col + 2)
         | #"'" :: rest =>
             SOME (#"'", rest, loc with col := loc.col + 2)
         | #"n" :: rest =>
             SOME (#"\n", rest, loc with col := loc.col + 2)
         | #"r" :: rest =>
             SOME (#"\r", rest, loc with col := loc.col + 2)
         | #"t" :: rest =>
             SOME (#"\t", rest, loc with col := loc.col + 2)
         | #"b" :: rest =>
             SOME (#"\b", rest, loc with col := loc.col + 2)
         | #" " :: rest =>
             SOME (#" ", rest, loc with col := loc.col + 2)
         | #"x" :: d1 :: d2 :: rest =>
             if isHexDigit d1 ∧ isHexDigit d2 then
               let n = hex2num [d1; d2] in
                 SOME (CHR n, rest, loc with col := loc.col + 4)
             else
               NONE
         | #"o" :: d1 :: d2 :: d3 :: rest =>
            if 48 ≤ ORD d1 ∧ ORD d1 ≤ 51 ∧ isOctDigit d2 ∧ isOctDigit d3 then
              let n = oct2num [d1; d2; d3] in
               SOME (CHR n, rest, loc with col := loc.col + 5)
             else
               NONE
         | d1 ::d2::d3::rest =>
             if EVERY isDigit [d1; d2; d3] then
               let n = dec2num [d1; d2; d3] in
                 if n ≤ 255 then
                   SOME (CHR n, rest, loc with col := loc.col + 4)
                 else
                   NONE
             else
               NONE
         | _ => NONE)
    | _ => NONE
End

Theorem scan_escseq_thm:
  ∀xs loc c ys loc'.
    scan_escseq xs loc = SOME (c, ys, loc') ⇒ LENGTH ys < LENGTH xs
Proof
  Induct \\ gs [scan_escseq_def]
  \\ rw [CaseEqs ["option", "string", "bool"]] \\ gs []
QED

Definition scan_strlit_def:
  scan_strlit acc cs loc =
    case cs of
      [] => SOME (ErrorS, Locs loc loc, cs)
    | #"\""::cs =>
        SOME (StringS (REVERSE acc),
              Locs loc (loc with col := loc.col),
              cs)
    | #"\n"::cs =>
        SOME (ErrorS,
              Locs loc (loc with <| col := 0; row := loc.row + 1 |>),
              cs)
    | #"\\"::_ =>
        (case scan_escseq cs loc of
           NONE => SOME (ErrorS, Locs loc loc, cs)
         | SOME (c, cs', loc') => scan_strlit (c::acc) cs' loc')
    | c::cs => scan_strlit (c::acc) cs (loc with col := loc.col + 1)
Termination
  wf_rel_tac ‘measure (LENGTH o FST o SND)’ \\ rw []
  \\ drule_then assume_tac scan_escseq_thm \\ gs []
End

Definition scan_charlit_def:
  scan_charlit cs loc =
    if cs = "" then
      SOME (ErrorS, Locs loc loc, cs)
    else if HD cs = #"\\" then
      case scan_escseq cs loc of
        SOME (c, cs', loc') =>
          if cs' ≠ "" ∧ HD cs' = #"'" then
            SOME (CharS c, Locs loc (loc' with col := loc'.col), TL cs')
          else
            SOME (ErrorS, Locs loc loc', cs')
      | NONE =>
          SOME (ErrorS, Locs loc loc, cs)
    else
      case cs of
        c :: #"'" :: rest =>
          SOME (CharS c, Locs loc (loc with col := loc.col + 1), rest)
      | _ =>
          SOME (ErrorS, Locs loc loc, cs)
End

Definition scan_number_def:
  scan_number ok_digit to_int offset cs loc =
    if cs = "" then
      SOME (ErrorS, Locs loc loc, cs)
    else if ¬ok_digit (HD cs) then
      SOME (ErrorS, Locs loc loc, cs)
    else
      let (cs', rest) = take_while (λc. c = #"_" ∨ ok_digit c) cs in
      let n = FILTER ($≠ #"_") cs' in
      let (t, rest) = if rest ≠ "" ∧ MEM (HD rest) "lLn"
                      then (1, TL rest)
                      else (0, rest) in
        SOME (NumberS (to_int n),
              Locs loc (loc with col := loc.col + LENGTH cs' + offset + t),
              rest)
End

Definition isSym_def:
  isSym c ⇔ MEM c "#$&*+-/=>@^|~!?%<:."
End

Definition isDelim_def:
  isDelim c ⇔ MEM c "()[]{}"
End

Definition next_sym_def:
  next_sym [] loc = NONE ∧
  next_sym (c::cs) loc =
    if c = #"\n" then
      next_sym cs (loc with <| col := 0; row := loc.row + 1 |>)
    else if isSpace c then
      next_sym cs (loc with col := loc.col + 1)
    else if isDigit c then
      if c = #"0" ∧ cs ≠ "" then
        if HD cs = #"x" ∨ HD cs = #"X" then
          scan_number isHexDigit (λs. &hex2num s) 2 (TL cs) loc
        else if HD cs = #"o" ∨ HD cs = #"O" then
          scan_number isOctDigit (λs. &oct2num s) 2 (TL cs) loc
        else if HD cs = #"b" ∨ HD cs = #"B" then
          scan_number isBinDigit (λs. &bin2num s) 2 (TL cs) loc
        else
          scan_number isDigit (λs. &dec2num s) 0 (c::cs) loc
      else
        scan_number isDigit (λs. &dec2num s) 0 (c::cs) loc
    else if c = #"-" ∧ cs ≠ "" ∧ isDigit (HD cs) then
      let (c, cs) = (HD cs, TL cs) in
        if c = #"0" ∧ cs ≠ "" then
          if HD cs = #"x" ∨ HD cs = #"X" then
            scan_number isHexDigit (λs. -&hex2num s) 2 (TL cs) loc
          else if HD cs = #"o" ∨ HD cs = #"O" then
            scan_number isOctDigit (λs. -&oct2num s) 2 (TL cs) loc
          else if HD cs = #"b" ∨ HD cs = #"B" then
            scan_number isBinDigit (λs. -&bin2num s) 2 (TL cs) loc
          else
            scan_number isDigit (λs. -&dec2num s) 0 (c::cs) loc
        else
          scan_number isDigit (λs. -&dec2num s) 0 (c::cs) loc
    else if c = #"\"" then
      scan_strlit [] cs (loc with col := loc.col + 1)
    else if c = #"'" ∧ cs ≠ "" then
      scan_charlit cs (loc with col := loc.col + 1)
    else if isPREFIX "*)" (c::cs) then
      SOME (ErrorS, Locs loc (loc with col := loc.col + 2), TL cs)
    else if isPREFIX [#"("; #"*"] (c::cs) then
      case skip_comment (TL cs) 0 (loc with col := loc.col + 2) of
      | NONE => SOME (ErrorS, Locs loc (loc with col := loc.col + 2), "")
      | SOME (rest, loc') => next_sym rest loc'
    else if isDelim c then
      SOME (OtherS [c], Locs loc loc, cs)
    else if isSym c then
      let (n, rest) = take_while isSym (c::cs) in
        SOME (OtherS n,
              Locs loc (loc with col := loc.col + LENGTH n - 1),
              rest)
    else if isAlpha c ∨ c = #"_" then
      let (n, rest) = take_while (λc. isAlphaNum c ∨ MEM c "'_") (c::cs) in
        SOME (OtherS n,
              Locs loc (loc with col := loc.col + LENGTH n - 1),
              rest)
    else
      NONE
Termination
  wf_rel_tac ‘measure (LENGTH o FST)’
  \\ rw [] \\ gs []
  \\ Cases_on ‘cs’ \\ gs []
  \\ drule skip_comment_thm \\ gs []
End

(*
EVAL “next_sym "-0X2f" loc”
EVAL “next_sym "0x2f" loc”
EVAL “next_sym "0b10n" loc”
EVAL “next_sym "0o77_3" loc”
EVAL “next_sym "-1_000_099L" loc”
EVAL “next_sym "' '" loc”
EVAL “next_sym "'\\033'" loc”
EVAL “next_sym (STRCAT "'\\" "x1f'") loc”
EVAL “next_sym "'\\o015'" loc”
EVAL “next_sym "(* foo (* bar *) baz 33 \n *) -4_4_n_rest" loc”
EVAL “next_sym ("\"foo " ++ #"\\" :: #"\\" :: " f\"") loc”
EVAL “next_sym "(* foo *)\"\\nfoo foofo\"" loc”
EVAL “scan_escseq [#"\\"; #"n"] loc”

EVAL “next_sym "foo39_'2 = bar" loc”
EVAL “next_sym "= bar" loc”

EVAL “next_sym "(= bar)" loc”
EVAL “next_sym "=<! bar" loc”
 *)

val _ = export_theory ();

