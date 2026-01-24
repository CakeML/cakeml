(*
  Lexer for the OCaml frontend.
 *)
Theory caml_lex
Ancestors
  misc[qualified] location lexer_impl lexer_fun[qualified]
Libs
  preamble


val _ = numLib.prefer_num ();

val _ = patternMatchesSyntax.temp_enable_pmatch();

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
    | SealT | AnyT | BtickT | TildeT | LqbraceT | RqbraceT | LqbrackT
    | RqbrackT | RrbrackT | LlbrackT | RlbrackT
    (* special HOL Light tokens (all infixes): *)
    | FuncompT | F_FT
    | THEN_T | THENC_T | THENL_T | THEN_TCL_T
    | ORELSE_T | ORELSEC_T | ORELSE_TCL_T
    (* CakeML pragma *)
    | PragmaT mlstring
    (* literals and identifiers: *)
    | IntT int
    | FloatT mlstring
    | CharT char
    | StringT mlstring
    | IdentT mlstring
    | SymbolT mlstring    (* symbols *)
    | LexErrorT
End

Definition isInt_def:
  isInt (IntT i) = T ∧
  isInt _ = F
End

Definition destInt_def[simp]:
  destInt (IntT i) = SOME i ∧
  destInt _ = NONE
End

Theorem isInt_thm:
  isInt x ⇔ ∃y. x = IntT y
Proof
  Cases_on ‘x’ \\ rw [isInt_def]
QED

Definition isFloat_def:
  isFloat (FloatT s) = T ∧
  isFloat _ = F
End

Definition destFloat_def[simp]:
  destFloat (FloatT s) = SOME s ∧
  destFloat _ = NONE
End

Theorem isFloat_thm:
  isFloat x ⇔ ∃y. x = FloatT y
Proof
  Cases_on ‘x’ \\ rw [isFloat_def]
QED

Definition isChar_def:
  isChar (CharT c) = T ∧
  isChar _ = F
End

Definition destChar_def[simp]:
  destChar (CharT c) = SOME c ∧
  destChar _ = NONE
End

Theorem isChar_thm:
  isChar x ⇔ ∃y. x = CharT y
Proof
  Cases_on ‘x’ \\ rw [isChar_def]
QED

Definition isString_def:
  isString (StringT s) = T ∧
  isString _ = F
End

Definition destString_def[simp]:
  destString (StringT s) = SOME s ∧
  destString _ = NONE
End

Theorem isString_thm:
  isString x ⇔ ∃y. x = StringT y
Proof
  Cases_on ‘x’ \\ rw [isString_def]
QED

Definition isSymbol_def:
  isSymbol (SymbolT s) = T ∧
  isSymbol _ = F
End

Definition destSymbol_def[simp]:
  destSymbol (SymbolT s) = SOME s ∧
  destSymbol _ = NONE
End

Theorem isSymbol_thm:
  isSymbol x ⇔ ∃y. x = SymbolT y
Proof
  Cases_on ‘x’ \\ rw [isSymbol_def]
QED

Definition isIdent_def:
  isIdent (IdentT s) = T ∧
  isIdent _ = F
End

Definition destIdent_def[simp]:
  destIdent (IdentT s) = SOME s ∧
  destIdent _ = NONE
End

Theorem isIdent_thm:
  isIdent x ⇔ ∃y. x = IdentT y
Proof
  Cases_on ‘x’ \\ rw [isIdent_def]
QED

Definition isPragma_def:
  isPragma (PragmaT s) = T ∧
  isPragma _ = F
End

Definition destPragma_def[simp]:
  destPragma (PragmaT s) = SOME s ∧
  destPragma _ = NONE
End

Theorem isPragma_thm:
  isPragma x ⇔ ∃y. x = PragmaT y
Proof
  Cases_on ‘x’ \\ rw [isPragma_def]
QED

(* -------------------------------------------------------------------------
 * Pre-tokens
 * ------------------------------------------------------------------------- *)

Datatype:
  symbol
    = NumberS int
    | FloatS string
    | StringS string
    | CharS char
    | OtherS string
    | PragmaS string
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
    pmatch xs of
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

Definition skip_comment_def:
  skip_comment cs d loc =
    pmatch cs of
      x::y::xs =>
        if x = #"(" ∧ y = #"*" then
          skip_comment xs (d + 1) (next_loc 2 loc)
        else if x = #"*" ∧ y = #")" then
          let loc' = next_loc 2 loc in
            if d = 0n then SOME (xs, loc') else skip_comment xs (d - 1) loc'
        else if x = #"\n" then
          skip_comment (y::xs) d (next_line loc)
        else
          skip_comment (y::xs) d (next_loc 1 loc)
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
    pmatch s of
      #"\\" :: cs =>
        (pmatch cs of
           #"\\" :: rest =>
             SOME (#"\\", rest, next_loc 2 loc)
         | #"\"" :: rest =>
             SOME (#"\"", rest, next_loc 2 loc)
         | #"'" :: rest =>
             SOME (#"'", rest, next_loc 2 loc)
         | #"n" :: rest =>
             SOME (#"\n", rest, next_loc 2 loc)
         | #"r" :: rest =>
             SOME (#"\r", rest, next_loc 2 loc)
         | #"t" :: rest =>
             SOME (#"\t", rest, next_loc 2 loc)
         | #"b" :: rest =>
             SOME (#"\b", rest, next_loc 2 loc)
         | #" " :: rest =>
             SOME (#" ", rest, next_loc 2 loc)
         | #"x" :: d1 :: d2 :: rest =>
             if isHexDigit d1 ∧ isHexDigit d2 then
               let n = hex2num [d1; d2] in
                 SOME (CHR n, rest, next_loc 4 loc)
             else
               NONE
         | #"o" :: d1 :: d2 :: d3 :: rest =>
            if 48 ≤ ORD d1 ∧ ORD d1 ≤ 51 ∧ isOctDigit d2 ∧ isOctDigit d3 then
              let n = oct2num [d1; d2; d3] in
               SOME (CHR n, rest, next_loc 5 loc)
             else
               NONE
         | d1 ::d2::d3::rest =>
             if EVERY isDigit [d1; d2; d3] then
               let n = dec2num [d1; d2; d3] in
                 if n ≤ 255 then
                   SOME (CHR n, rest, next_loc 4 loc)
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
    pmatch cs of
      [] => SOME (ErrorS, Locs loc loc, cs)
    | #"\""::cs =>
        SOME (StringS (REVERSE acc), Locs loc loc, cs)
    | #"\n"::cs =>
        SOME (ErrorS, Locs loc (next_line loc), cs)
    | #"\\"::_ =>
        (pmatch scan_escseq cs loc of
           NONE => SOME (ErrorS, Locs loc loc, cs)
         | SOME (c, cs', loc') => scan_strlit (c::acc) cs' loc')
    | c::cs => scan_strlit (c::acc) cs (next_loc 1 loc)
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
      pmatch scan_escseq cs loc of
        SOME (c, cs', loc') =>
          if cs' ≠ "" ∧ HD cs' = #"'" then
            SOME (CharS c, Locs loc loc', TL cs')
          else
            SOME (ErrorS, Locs loc loc', cs')
      | NONE =>
          SOME (ErrorS, Locs loc loc, cs)
    else
      pmatch cs of
        c :: #"'" :: rest =>
          SOME (CharS c, Locs loc (next_loc 1 loc), rest)
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
              Locs loc (next_loc (LENGTH cs' + offset + t - 1) loc),
              rest)
End

(* FLOATS
 *
 *   float-lit ::= [0-9] [0-9_]* ("." [0-9_]* )? ([eE] [+-]? [0-9_]* )?
 *
 *)

(* [0-9] [0-9_]* *)
Definition scan_float1_def:
  scan_float1 cs =
    if cs = "" ∨ ¬isDigit (HD cs) then NONE else
      let (cs', rest) = take_while (λc. c = #"_" ∨ isDigit c) cs in
      let n = FILTER ($≠ #"_") cs' in
        SOME (n, LENGTH cs', rest)
End

(* "." [0-9_]* *)
Definition scan_float2_def:
  scan_float2 cs =
    if cs = "" ∨ HD cs ≠ #"." then NONE else
      let (cs', rest) = take_while (λc. c = #"_" ∨ isDigit c) (TL cs) in
      let n = FILTER ($≠ #"_") cs' in
        SOME (#"." :: n, LENGTH cs' + 1, rest)
End

(* [eE] [+-]? *)
Definition scan_float3_def:
  scan_float3 cs =
    pmatch cs of
      x :: y :: rest =>
        if ¬MEM x "eE" then NONE
        else if MEM y "+-" then
          if rest = "" ∨ ¬isDigit (HD rest) then NONE else
            let (cs', rest') = take_while (λc. c = #"_" ∨ isDigit c) rest in
            let n = FILTER ($≠ #"_") cs' in
              SOME (x::y::n, 2 + LENGTH cs', rest')
        else if ¬isDigit y then NONE
        else
          let (cs', rest') = take_while (λc. c = #"_" ∨ isDigit c) rest in
          let n = FILTER ($≠ #"_") cs' in
            SOME (x::y::n, 2 + LENGTH cs', rest')
    | _ => NONE
End

(* At least one of scan_float2 or scan_float3 must succeed. If they fail,
 * try to scan an integer instead.
 *)
Definition scan_float_or_int_def:
  scan_float_or_int cs loc =
    pmatch scan_float1 cs of
      NONE => SOME (ErrorS, Locs loc loc, cs)
    | SOME (s1, n1, cs1) =>
        pmatch scan_float2 cs1 of
          NONE =>
            (* try scan_float3 *)
            (pmatch scan_float3 cs1 of
              NONE => scan_number isDigit (λs. &dec2num s) 0 cs loc
            | SOME (s2, n2, cs2) => SOME (FloatS (s1 ++ s2),
                                          Locs loc (next_loc (n1 + n2) loc),
                                          cs2))
        | SOME (s2, n2, cs2) =>
            (pmatch scan_float3 cs2 of
              NONE => SOME (FloatS (s1 ++ s2),
                            Locs loc (next_loc (n1 + n2) loc),
                            cs2)
            | SOME (s3, n3, cs3) =>
                SOME (FloatS (s1 ++ s2 ++ s3),
                      Locs loc (next_loc (n1 + n2 + n3) loc),
                      cs3))
End

Definition scan_pragma_def:
  scan_pragma (level: num) (n: num) cs loc =
  pmatch cs of
    x::y::xs =>
      if x = #"(" ∧ y = #"*" then
        scan_pragma (level + 1) (n + 2) xs (next_loc 2 loc)
      else if x = #"*" ∧ y = #")" then
        let loc' = next_loc 2 loc in
          if level = 0 then
            SOME (n, next_loc 2 loc, xs)
          else
            scan_pragma (level - 1) (n + 2) xs loc'
      else if x = #"\n" then
        scan_pragma level (n + 1) (y::xs) (next_line loc)
      else
        scan_pragma level (n + 1) (y::xs) (next_loc 1 loc)
  | _ => NONE
End

Theorem scan_pragma_thm:
  ∀l n cs loc m loc' rest.
    scan_pragma l n cs loc = SOME (m, loc', rest) ⇒
      LENGTH rest ≤ LENGTH cs ∧
      n ≤ m
Proof
  ho_match_mp_tac scan_pragma_ind \\ rw []
  \\ rgs [Once scan_pragma_def, CaseEqs ["option", "list", "bool"]]
  \\ gvs []
QED

Theorem scan_number_thm:
  scan_number f g off cs loc = SOME (sym, locs, ds) ⇒
    LENGTH ds ≤ LENGTH cs
Proof
  rw [scan_number_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ drule_then assume_tac take_while_thm \\ gs []
  \\ gvs [NOT_NIL_EQ_LENGTH_NOT_0, LENGTH_TL, CaseEq "bool"]
QED

Theorem scan_float_or_int_thm:
  scan_float_or_int cs loc = SOME (sym, locs, ds) ⇒ LENGTH ds ≤ LENGTH cs
Proof
  simp [scan_float_or_int_def, scan_float1_def, scan_float2_def,
        scan_float3_def, CaseEqs ["prod", "string", "option", "bool"],
        IS_SOME_EXISTS]
  \\ rw [] \\ gvs [UNCURRY_eq_pair, NOT_NIL_EQ_LENGTH_NOT_0]
  \\ imp_res_tac take_while_thm \\ gs [LENGTH_TL]
  \\ imp_res_tac scan_number_thm \\ gs []
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
      next_sym cs (next_line loc)
    else if isSpace c then
      next_sym cs (next_loc 1 loc)
    else if isDigit c then
      if c = #"0" ∧ cs ≠ "" then
        if HD cs = #"x" ∨ HD cs = #"X" then
          scan_number isHexDigit (λs. &hex2num s) 2 (TL cs) loc
        else if HD cs = #"o" ∨ HD cs = #"O" then
          scan_number isOctDigit (λs. &oct2num s) 2 (TL cs) loc
        else if HD cs = #"b" ∨ HD cs = #"B" then
          scan_number isBinDigit (λs. &bin2num s) 2 (TL cs) loc
        else
          scan_float_or_int (c::cs) loc
      else
        scan_float_or_int (c::cs) loc
    else if c = #"\"" then
      scan_strlit [] cs (next_loc 1 loc)
    else if c = #"'" then
      pmatch scan_charlit cs (next_loc 1 loc) of
      | NONE => SOME (OtherS [c], Locs loc loc, cs)
      | SOME res =>
          if FST res = ErrorS then SOME (OtherS [c], Locs loc loc, cs)
          else SOME res
    else if isPREFIX "*)" (c::cs) then
      SOME (ErrorS, Locs loc (next_loc 2 loc), TL cs)
    else if isPREFIX (#"(" :: #"*" :: "CML") (c::cs) then
      pmatch scan_pragma 0 0 (DROP 4 cs) loc of
      | NONE => SOME (ErrorS, Locs loc loc, "")
      | SOME (n, loc', rest) =>
          SOME (PragmaS (TAKE n (DROP 4 cs)),
                Locs loc loc',
                rest)
    else if isPREFIX [#"("; #"*"] (c::cs) then
      pmatch skip_comment (TL cs) 0 (next_loc 2 loc) of
      | NONE => SOME (ErrorS, Locs loc (next_loc 2 loc), "")
      | SOME (rest, loc') => next_sym rest loc'
    else if isDelim c then
      SOME (OtherS [c], Locs loc loc, cs)
    else if isSym c then
      let (n, rest) = take_while isSym (c::cs) in
        SOME (OtherS n,
              Locs loc (next_loc (LENGTH n - 1) loc),
              rest)
    else if isAlpha c ∨ c = #"_" then
      let (n, rest) = take_while (λc. isAlphaNum c ∨ MEM c "'_") (c::cs) in
        SOME (OtherS n,
              Locs loc (next_loc (LENGTH n - 1) loc),
              rest)
    else
      SOME (ErrorS, Locs loc loc, cs)
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

Theorem scan_float2_thm[local]:
  scan_float2 cs = SOME (s, n, ds) ⇒
    0 < n ∧
    LENGTH cs = n + LENGTH ds
Proof
  rw [scan_float2_def, UNCURRY_eq_pair] \\ gs []
  \\ drule_then assume_tac take_while_thm
  \\ gs [NOT_NIL_EQ_LENGTH_NOT_0, LENGTH_TL]
QED

Theorem scan_float3_thm[local]:
  scan_float3 cs = SOME (s, n, ds) ⇒
    0 < n ∧
    LENGTH cs = n + LENGTH ds
Proof
  rw [scan_float3_def, UNCURRY_eq_pair] \\ gs []
  \\ gvs [CaseEqs ["string", "bool", "option"], UNCURRY_eq_pair]
  \\ drule_then assume_tac take_while_thm
  \\ gs [NOT_NIL_EQ_LENGTH_NOT_0, LENGTH_TL]
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
    scan_float_or_int_thm,
    scan_number_thm,
    scan_strlit_thm] \\ gs []
  \\ gs [CaseEqs ["option", "prod", "bool"], UNCURRY_eq_pair]
  \\ imp_res_tac scan_charlit_thm
  (* Various scan_number calls: *)
  \\ TRY (gs [NOT_NIL_EQ_LENGTH_NOT_0, LENGTH_TL] \\ NO_TAC)
  (* Two identical scan_float goals: *)
  \\ TRY (
    qpat_x_assum ‘scan_float_or_int _ _ = _’ mp_tac
    \\ simp [scan_float_or_int_def]
    \\ CASE_TAC \\ gs []
    \\ gvs [scan_float1_def, UNCURRY_eq_pair]
    \\ rw [CaseEqs ["option", "prod"]] \\ gs []
    \\ gvs [scan_number_def, UNCURRY_eq_pair, CaseEq "bool"]
    \\ map_every imp_res_tac [
        scan_float2_thm,
        scan_float3_thm,
        take_while_thm]
    \\ gs [NOT_NIL_EQ_LENGTH_NOT_0, LENGTH_TL]
    \\ gs [take_while_def]
    \\ drule_at (Pos (el 3)) take_while_lemma \\ gs [])
  \\ map_every imp_res_tac [
      scan_pragma_thm,
      skip_comment_thm] \\ gs []
  \\ Cases_on ‘cs’ \\ gs []
  \\ Cases_on ‘ds’ \\ gs []
  \\ imp_res_tac take_while_thm \\ gvs []
  \\ gs [take_while_def, isAlphaNum_def]
  \\ imp_res_tac take_while_lemma \\ gvs []
  \\ gs [take_while_aux_def]
QED

(*
EVAL “next_sym "(*CML (* foo *) bar *)" loc”

EVAL “next_sym "'foo'" loc”
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

EVAL “next_sym "*" loc”

EVAL “next_sym "123.456e+33" loc”
EVAL “next_sym "123.456E33" loc”
EVAL “next_sym "123." loc”
EVAL “next_sym "0.3e" loc”

 *)

Definition get_token_def:
  get_token s =
    if s = "" then LexErrorT else
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
    if s = "end" then EndT else
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
    (* HOL Light: *)
    if s = "o" then FuncompT else
    if s = "F_F" then F_FT else
    if s = "THEN" then THEN_T else
    if s = "THENC" then THENC_T else
    if s = "THENL" then THENL_T else
    if s = "THEN_TCL" then THEN_TCL_T else
    if s = "ORELSE" then ORELSE_T else
    if s = "ORELSEC" then ORELSEC_T else
    if s = "ORELSE_TCL" then ORELSE_TCL_T else
    (* identifiers or symbols *)
      let c = HD s in
        if isAlpha c ∨ c = #"_" then IdentT (implode s) else
          SymbolT (implode s)
End

Definition sym2token_def:
  sym2token s =
    pmatch s of
      NumberS i => IntT i
    | FloatS s => FloatT (implode s)
    | StringS s => StringT (implode s)
    | CharS c => CharT c
    | ErrorS => LexErrorT
    | PragmaS s => PragmaT (implode s)
    | OtherS s => get_token s
End

Definition next_token_def:
  next_token inp loc =
    pmatch next_sym inp loc of
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
EVAL “next_token "* /" loc”
EVAL “next_token "**" loc”
EVAL “next_token "(*CML (* foo bar *) baz\n\nasdf*)" loc”
EVAL “next_token "(* CML (* foo bar *) baz\n\nasdf*)" loc” (* = NONE *)
EVAL “next_token "(*CL (* foo bar *) baz\n\nasdf*)" loc” (* = NONE *)
 *)

Definition lexer_fun_aux_def:
  lexer_fun_aux inp loc =
    pmatch next_token inp loc of
      NONE => []
    | SOME (tok, Locs loc1 loc2, rest) =>
        (tok, Locs loc1 loc2) ::
          lexer_fun_aux rest (next_loc 1 loc2)
Termination
  wf_rel_tac ‘measure (LENGTH o FST)’ \\ rw []
  \\ drule_then assume_tac next_token_thm \\ gs []
End

Definition lexer_fun_def:
  lexer_fun inp = lexer_fun_aux inp init_loc
End

(*
EVAL “lexer_fun "true"”
EVAL “lexer_fun "false"”
EVAL “lexer_fun "()"”
EVAL “lexer_fun "begin end"”
EVAL “lexer_fun "( )"”
EVAL “lexer_fun "X.x"”
EVAL “lexer_fun "x"”
EVAL “lexer_fun "3 <+> 5 FOO"”
EVAL “lexer_fun "4;;\n(*CML code *)"”
 *)

(* -------------------------------------------------------------------------
 * PMATCH
 * ------------------------------------------------------------------------- *)

val PMCONV = patternMatchesLib.PMATCH_ELIM_CONV;

Theorem isInt_PMATCH:
  ∀x. isInt x =
        pmatch x of
          IntT i => T
        | _ => F
Proof
  CONV_TAC (DEPTH_CONV PMCONV)
  \\ Cases \\ rw [isInt_def]
QED

Theorem destInt_PMATCH:
  ∀x. destInt x =
        pmatch x of
          IntT i => SOME i
        | _ => NONE
Proof
  CONV_TAC (DEPTH_CONV PMCONV)
  \\ Cases \\ rw []
QED

Theorem isFloat_PMATCH:
  ∀x. isFloat x =
        pmatch x of
          FloatT i => T
        | _ => F
Proof
  CONV_TAC (DEPTH_CONV PMCONV)
  \\ Cases \\ rw [isFloat_def]
QED

Theorem destFloat_PMATCH:
  ∀x. destFloat x =
        pmatch x of
          FloatT i => SOME i
        | _ => NONE
Proof
  CONV_TAC (DEPTH_CONV PMCONV)
  \\ Cases \\ rw []
QED

Theorem isChar_PMATCH:
  ∀x. isChar x =
        pmatch x of
          CharT c => T
        | _ => F
Proof
  CONV_TAC (DEPTH_CONV PMCONV)
  \\ Cases \\ rw [isChar_def]
QED

Theorem destChar_PMATCH:
  ∀x. destChar x =
        pmatch x of
          CharT c => SOME c
        | _ => NONE
Proof
  CONV_TAC (DEPTH_CONV PMCONV)
  \\ Cases \\ rw []
QED

Theorem isString_PMATCH:
  ∀x. isString x =
        pmatch x of
          StringT s => T
        | _ => F
Proof
  CONV_TAC (DEPTH_CONV PMCONV)
  \\ Cases \\ rw [isString_def]
QED

Theorem destString_PMATCH:
  ∀x. destString x =
        pmatch x of
          StringT s => SOME s
        | _ => NONE
Proof
  CONV_TAC (DEPTH_CONV PMCONV)
  \\ Cases \\ rw [isString_def]
QED

Theorem isSymbol_PMATCH:
  ∀x. isSymbol x =
        pmatch x of
          SymbolT s => T
        | _ => F
Proof
  CONV_TAC (DEPTH_CONV PMCONV)
  \\ Cases \\ rw [isSymbol_def]
QED

Theorem destSymbol_PMATCH:
  ∀x. destSymbol x =
        pmatch x of
          SymbolT s => SOME s
        | _ => NONE
Proof
  CONV_TAC (DEPTH_CONV PMCONV)
  \\ Cases \\ rw [isSymbol_def]
QED

Theorem isIdent_PMATCH:
  ∀x. isIdent x =
        pmatch x of
          IdentT s => T
        | _ => F
Proof
  CONV_TAC (DEPTH_CONV PMCONV)
  \\ Cases \\ rw [isIdent_def]
QED

Theorem destIdent_PMATCH:
  ∀x. destIdent x =
        pmatch x of
          IdentT s => SOME s
        | _ => NONE
Proof
  CONV_TAC (DEPTH_CONV PMCONV)
  \\ Cases \\ rw []
QED

Theorem isPragma_PMATCH:
  ∀x. isPragma x =
        pmatch x of
          PragmaT s => T
        | _ => F
Proof
  CONV_TAC (DEPTH_CONV PMCONV)
  \\ Cases \\ rw [isPragma_def]
QED

Theorem destPragma_PMATCH:
  ∀x. destPragma x =
        pmatch x of
          PragmaT s => SOME s
        | _ => NONE
Proof
  CONV_TAC (DEPTH_CONV PMCONV)
  \\ Cases \\ rw []
QED
