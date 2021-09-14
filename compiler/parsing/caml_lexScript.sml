(*
  Lexer for the caml frontend.
 *)

open preamble locationTheory;

val _ = new_theory "caml_lex";

(* TODO
 * - Location spans might be wrong just about everywhere
 * - infix symbols mix with other symbols
 *)

(* -------------------------------------------------------------------------
 * Tokens
 * ------------------------------------------------------------------------- *)

Datatype:
  token
    (* keywords: *)
    = AndT | AsT | AssertT | AsrT | BeginT | ClassT | ConstraintT | DoT | DoneT
    | DowntoT | ElseT | EndT | ExceptionT | ExternalT | FalseT | ForT | FunT
    | FunctionT | FunctorT | IfT | InT | IncludeT | InheritT | InitializerT
    | LandT | LazyT | LetT | LorT | LslT | LsrT | LxorT | MatchT | MethodT
    | ModT | ModuleT | MutableT | NewT | NonrecT | ObjectT | OfT | OpenT | OrT
    | PrivateT | RecT | SigT | StructT | ThenT | ToT | TrueT | TryT | TypeT
    | ValT | VirtualT | WhenT | WhileT | WithT
    (* symbol keywords: *)
    | EqualT | TickT | LparT | RparT | HashT | StarT | PlusT | CommaT | MinusT
    | LessT | GreaterT | LbrackT | RbrackT | LbraceT | RbraceT | QuestionT
    | SemiT | SemisT | BarT | OrelseT | AmpT | AndalsoT | NeqT | MinusFT
    | RarrowT | LarrowT | DotT | DotsT | EscapeT | ColonT | ColonsT | UpdateT
    | SealT | AnyT | BtickT | TildeT | LqbraceT | RqbraceT | LqbrackT | RqbrackT
    | RrbrackT | LlbrackT | RlbrackT
    (* literals and identifiers: *)
    | IntT int
    | CharT char
    | StringT string
    | IdentT string
    | SymbolT string    (* symbols *)
    | LexErrorT
End

Definition isInt_def:
  isInt (IntT i) = T ∧
  isInt _ = F
End

Definition destInt_def:
  destInt (IntT i) = SOME i ∧
  destInt _ = NONE
End

Definition isChar_def:
  isChar (CharT c) = T ∧
  isChar _ = F
End

Definition destChar_def:
  destChar (CharT c) = SOME c ∧
  destChar _ = NONE
End

Definition isString_def:
  isString (StringT s) = T ∧
  isString _ = F
End

Definition destString_def:
  destString (StringT s) = SOME s ∧
  destString _ = NONE
End

Definition isSymbol_def:
  isSymbol (SymbolT s) = T ∧
  isSymbol _ = F
End

Definition destSymbol_def:
  destSymbol (SymbolT s) = SOME s ∧
  destSymbol _ = NONE
End

Definition isIdent_def:
  isIdent (IdentT s) = T ∧
  isIdent _ = F
End

Definition destIdent_def:
  destIdent (IdentT s) = SOME s ∧
  destIdent _ = NONE
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

Theorem take_while_aux_thm[local]:
  ∀acc p xs ys zs.
    take_while_aux acc p xs = (ys, zs) ⇒
      LENGTH xs + LENGTH acc = LENGTH ys + LENGTH zs
Proof
  ho_match_mp_tac take_while_aux_ind \\ rw []
  \\ pop_assum mp_tac
  \\ simp [Once take_while_aux_def]
  \\ CASE_TAC \\ gs []
  \\ rw [] \\ gs []
QED

Definition take_while_def:
  take_while = take_while_aux []
End

Theorem take_while_thm:
  take_while p xs = (ys, zs) ⇒ LENGTH xs = LENGTH ys + LENGTH zs
Proof
  rw [take_while_def]
  \\ drule_then assume_tac take_while_aux_thm
  \\ gs []
QED

Definition loc_row_def:
  loc_row n = <| row := n; col := 1; offset := 0 |>
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
          skip_comment (y::xs) d (loc_row (loc.row + 1))
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

Theorem scan_strlit_thm:
  ∀acc cs loc sym locs ds.
    scan_strlit acc cs loc = SOME (sym, locs, ds) ⇒
      LENGTH ds ≤ LENGTH cs + LENGTH acc
Proof
  ho_match_mp_tac scan_strlit_ind \\ rw []
  \\ pop_assum mp_tac
  \\ simp [Once scan_strlit_def]
  \\ rw [CaseEqs ["string", "option", "prod", "bool"]] \\ gs []
  \\ imp_res_tac scan_escseq_thm \\ gs []
QED

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

Theorem scan_charlit_thm:
  scan_charlit cs loc = SOME (sym, locs, ds) ⇒ LENGTH ds ≤ LENGTH cs
Proof
  rw [scan_charlit_def, CaseEqs ["option", "prod", "bool", "string"]] \\ gs []
  \\ imp_res_tac scan_escseq_thm
  \\ gs [NOT_NIL_EQ_LENGTH_NOT_0, LENGTH_TL]
QED

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

Theorem scan_number_thm:
  scan_number f g off cs loc = SOME (sym, locs, ds) ⇒
    LENGTH ds ≤ LENGTH cs
Proof
  rw [scan_number_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ drule_then assume_tac take_while_thm \\ gs []
  \\ gvs [NOT_NIL_EQ_LENGTH_NOT_0, LENGTH_TL, CaseEq "bool"]
QED

Definition isSym_def:
  isSym c ⇔ MEM c "#$&*+-/=>@^|~!?%<:.;"
End

Definition isDelim_def:
  isDelim c ⇔ MEM c "()[]{},"
End

Definition next_sym_def:
  next_sym [] loc = NONE ∧
  next_sym (c::cs) loc =
    if c = #"\n" then
      next_sym cs (loc_row (loc.row + 1))
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

Theorem take_while_lemma[local]:
  ∀acc p xs ys zs.
    xs ≠ "" ∧
    p (HD xs) ∧
    take_while_aux acc p xs = (ys, zs) ⇒
      0 < LENGTH ys
Proof
  ho_match_mp_tac take_while_aux_ind \\ rw []
  \\ pop_assum mp_tac
  \\ simp [Once take_while_aux_def]
  \\ CASE_TAC \\ gs []
  \\ rw [] \\ gs []
  \\ pop_assum mp_tac
  \\ simp [Once take_while_aux_def]
  \\ CASE_TAC \\ gs [] \\ rw [] \\ gs []
QED

Theorem next_sym_thm:
  ∀cs loc sym locs ds.
    next_sym cs loc = SOME (sym, locs, ds) ⇒
      LENGTH ds < LENGTH cs
Proof
  ho_match_mp_tac next_sym_ind \\ rw []
  \\ simp [next_sym_def]
  \\ pop_assum mp_tac
  \\ rw [Once next_sym_def] \\ gs []
  \\ map_every imp_res_tac [
    scan_number_thm,
    scan_strlit_thm,
    scan_charlit_thm ] \\ gs []
  \\ gs [NOT_NIL_EQ_LENGTH_NOT_0, LENGTH_TL]
  \\ imp_res_tac skip_comment_thm \\ gs []
  \\ imp_res_tac take_while_thm \\ gs []
  \\ gs [take_while_def, Once scan_number_def, isAlphaNum_def]
  \\ gvs [CaseEqs ["option", "prod", "bool"]]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [CaseEqs ["option", "prod", "bool"]]
  \\ imp_res_tac take_while_lemma \\ gs []
  \\ gs [GSYM take_while_def]
  \\ imp_res_tac take_while_thm
  \\ gs [NOT_NIL_EQ_LENGTH_NOT_0, LENGTH_TL]
  \\ Cases_on ‘cs’ \\ gs []
  \\ imp_res_tac skip_comment_thm \\ gs []
  \\ Cases_on ‘c’ \\ gs []
QED

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

Definition get_token_def:
  get_token s =
    if s = "=" then EqualT else
    if s = "'" then TickT else
    if s = "(" then LparT else
    if s = ")" then RparT else
    if s = "#" then HashT else
    if s = "*" then StarT else
    if s = "+" then PlusT else
    if s = "," then CommaT else
    if s = "-" then MinusT else
    if s = "<" then LessT else
    if s = ">" then GreaterT else
    if s = "[" then LbrackT else
    if s = "]" then RbrackT else
    if s = "{" then LbraceT else
    if s = "}" then RbraceT else
    if s = "?" then QuestionT else
    if s = ";" then SemiT else
    if s = ";;" then SemisT else
    if s = "|" then BarT else
    if s = "||" then OrelseT else
    if s = "&" then AmpT else
    if s = "&&" then AndalsoT else
    if s = "!=" then NeqT else
    if s = "-." then MinusFT else
    if s = "->" then RarrowT else
    if s = "<-" then LarrowT else
    if s = "." then DotT else
    if s = ".." then DotsT else
    if s = ".~" then EscapeT else
    if s = ":" then ColonT else
    if s = "::" then ColonsT else
    if s = ":=" then UpdateT else
    if s = ":>" then SealT else
    if s = "_" then AnyT else
    if s = "`" then BtickT else
    if s = "~" then TildeT else
    if s = "{<" then LqbraceT else
    if s = ">}" then RqbraceT else
    if s = "[<" then LqbrackT else
    if s = ">]" then RqbrackT else
    if s = "[>" then RrbrackT else
    if s = "[|" then LlbrackT else
    if s = "|]" then RlbrackT else
    if s = "and" then AndT else
    if s = "as" then AsT else
    if s = "assert" then AssertT else
    if s = "asr" then AsrT else
    if s = "begin" then BeginT else
    if s = "class" then ClassT else
    if s = "constraint" then ConstraintT else
    if s = "do" then DoT else
    if s = "done" then DoneT else
    if s = "downto" then DowntoT else
    if s = "else" then ElseT else
    if s = "exception" then ExceptionT else
    if s = "external" then ExternalT else
    if s = "false" then FalseT else
    if s = "for" then ForT else
    if s = "fun" then FunT else
    if s = "function" then FunctionT else
    if s = "functor" then FunctorT else
    if s = "if" then IfT else
    if s = "in" then InT else
    if s = "include" then IncludeT else
    if s = "inherit" then InheritT else
    if s = "initializer" then InitializerT else
    if s = "land" then LandT else
    if s = "lazy" then LazyT else
    if s = "let" then LetT else
    if s = "lor" then LorT else
    if s = "lsl" then LslT else
    if s = "lsr" then LsrT else
    if s = "lxor" then LxorT else
    if s = "match" then MatchT else
    if s = "method" then MethodT else
    if s = "mod" then ModT else
    if s = "module" then ModuleT else
    if s = "mutable" then MutableT else
    if s = "new" then NewT else
    if s = "nonrec" then NonrecT else
    if s = "object" then ObjectT else
    if s = "of" then OfT else
    if s = "open" then OpenT else
    if s = "or" then OrT else
    if s = "private" then PrivateT else
    if s = "rec" then RecT else
    if s = "sig" then SigT else
    if s = "struct" then StructT else
    if s = "then" then ThenT else
    if s = "to" then ToT else
    if s = "true" then TrueT else
    if s = "try" then TryT else
    if s = "type" then TypeT else
    if s = "val" then ValT else
    if s = "virtual" then VirtualT else
    if s = "when" then WhenT else
    if s = "while" then WhileT else
    if s = "with" then WithT else
    (* identifiers or symbols *)
    if s = "" then LexErrorT else
      let c = HD s in
        if isAlpha c ∨ c = #"_" then IdentT s else
          SymbolT s
End

Definition sym2token_def:
  sym2token s =
    case s of
      NumberS i => IntT i
    | StringS s => StringT s
    | CharS c => CharT c
    | ErrorS => LexErrorT
    | OtherS s => get_token s
End

Definition next_token_def:
  next_token inp loc =
    case next_sym inp loc of
      NONE => NONE
    | SOME (sym, locs, rest) => SOME (sym2token sym, locs, rest)
End

Theorem next_token_thm:
  next_token inp loc = SOME (sym, locs, rest) ⇒
    LENGTH rest < LENGTH inp
Proof
  rw [next_token_def, CaseEqs ["option", "prod"]]
  \\ drule_then assume_tac next_sym_thm \\ gs []
QED

(*
EVAL “next_token "let foo = 3;; (* bar *)" loc”
EVAL “next_token "-33 + 44" loc”
 *)

Definition lexer_fun_aux_def:
  lexer_fun_aux inp loc =
    case next_token inp loc of
      NONE => []
    | SOME (tok, Locs loc1 loc2, rest) =>
        (tok, Locs loc1 loc2) ::
          lexer_fun_aux rest (loc2 with col := loc2.col + 1)
Termination
  wf_rel_tac ‘measure (LENGTH o FST)’ \\ rw []
  \\ drule_then assume_tac next_token_thm \\ gs []
End

Definition init_loc_def:
  init_loc = <| row := 1; col := 1; offset := 0 |>
End

Definition lexer_fun_def:
  lexer_fun inp = lexer_fun_aux inp init_loc
End

val _ = export_theory ();

