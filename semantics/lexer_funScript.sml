open HolKernel Parse boolLib bossLib;

val _ = new_theory "lexer_fun";

open stringTheory stringLib listTheory TokensTheory ASCIInumbersTheory intLib;

(* This script defines the functional spec for the assmebly
   implementation of the lexer. This lexer specification consists of
   two phases. The first phase reads a string and returns a list of
   symbols. The second phase converts the symbol list into a list of
   tokens. The implementation merges these two phases. *)

(* intermediate symbols *)

val _ = Hol_datatype `symbol = StringS of string
                             | NumberS of num
                             | OtherS of string
                             | ErrorS `;

(* helper functions *)

val read_while_def = Define `
  (read_while P "" s = (IMPLODE (REVERSE s),"")) /\
  (read_while P (STRING c cs) s =
     if P c then read_while P cs (c :: s)
            else (IMPLODE (REVERSE s),STRING c cs))`;

val is_single_char_symbol_def = Define `
  is_single_char_symbol c = MEM c "()[];,_"`;

val isSymbol_def = Define `
  isSymbol c = (~(isSpace c) /\ ~(isDigit c) /\ ~(isAlpha c) /\
                ~is_single_char_symbol c /\ ORD #" " < ORD c /\ c <> #".")`;

val read_string_def = tDefine "read_string" `
  read_string str s =
    if str = "" then (ErrorS,"") else
    if HD str = #"\"" then (StringS s,TL str) else
    if HD str = #"\n" then (ErrorS,TL str) else
    if HD str <> #"\\" then read_string (TL str) (s ++ [HD str]) else
      case TL str of
      | #"\\"::cs => read_string cs (s ++ "\\")
      | #"\""::cs => read_string cs (s ++ "\"")
      | #"n"::cs => read_string cs (s ++ "\n")
      | #"t"::cs => read_string cs (s ++ "\t")
      | _ => (ErrorS,TL str)`
  (WF_REL_TAC `measure (LENGTH o FST)` THEN REPEAT STRIP_TAC
   THEN Cases_on `str` THEN FULL_SIMP_TAC (srw_ss()) [] THEN DECIDE_TAC)

val read_string_thm = prove(
  ``!s t x1 x2. (read_string s t = (x1,x2)) ==>
                (LENGTH x2 <= LENGTH s + LENGTH t)``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ]
  THEN HO_MATCH_MP_TAC (fetch "-" "read_string_ind")
  THEN REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC
  THEN ONCE_REWRITE_TAC [read_string_def]
  THEN Cases_on `s` THEN SIMP_TAC (srw_ss()) []
  THEN SRW_TAC [] [LENGTH] THEN RES_TAC THEN TRY DECIDE_TAC
  THEN SRW_TAC [] [LENGTH] THEN Cases_on `t'`
  THEN FULL_SIMP_TAC (srw_ss()) [] THEN CCONTR_TAC
  THEN Q.PAT_ASSUM `(x1,x2) = xxx` MP_TAC
  THEN SIMP_TAC std_ss [] THEN SRW_TAC [] []
  THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss []
  THEN RES_TAC THEN TRY DECIDE_TAC THEN CCONTR_TAC
  THEN FULL_SIMP_TAC std_ss [LENGTH] THEN DECIDE_TAC);

(* str_to_syms turns a string into a list of symbols *)

val skip_comment_def = Define `
  (skip_comment "" d = NONE) /\
  (skip_comment [x] d = NONE) /\
  (skip_comment (x::y::xs) d =
     if [x;y] = "(*" then skip_comment xs (d+1) else
     if [x;y] = "*)" then (if d = 0 then SOME xs else skip_comment xs (d-1))
     else skip_comment (y::xs) d)`

val skip_comment_thm = prove(
  ``!xs d str. (skip_comment xs d = SOME str) ==> LENGTH str <= LENGTH xs``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ]
  THEN HO_MATCH_MP_TAC (fetch "-" "skip_comment_ind") THEN REPEAT STRIP_TAC
  THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [skip_comment_def]
  THEN SRW_TAC [] [] THEN RES_TAC THEN TRY DECIDE_TAC
  THEN FULL_SIMP_TAC std_ss [] THEN SRW_TAC [] [] THEN RES_TAC THEN DECIDE_TAC);

val read_while_thm = prove(
  ``!cs s cs' s'.
       (read_while P cs s = (s',cs')) ==> STRLEN cs' <= STRLEN cs``,
  Induct THEN SRW_TAC [][read_while_def] THEN SRW_TAC [][] THEN
  RES_TAC THEN FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND] THEN DECIDE_TAC);

val isAlphaNumPrime_def = Define`
  isAlphaNumPrime c <=> isAlphaNum c ∨ c = #"'"
`

val moduleRead_def = Define`
  moduleRead initP c s =
    let (n,rest) = read_while initP s [c]
    in
      case rest of
          [] => (OtherS n, rest)
        | [h] => if h = #"." then (ErrorS, [])
                 else (OtherS n, rest)
        | h1::h2::rest' =>
          if h1 = #"." then
            let nextP = if isAlpha h2 then SOME isAlphaNumPrime
                        else if isSymbol h2 then SOME isSymbol
                        else NONE
            in
              case nextP of
                  NONE => (ErrorS, rest')
                | SOME P =>
                  let (n2, rest'') = read_while P rest' [h2]
                  in
                    (OtherS (n ++ "." ++ n2), rest'')
          else (OtherS n, rest)
`

val moduleRead_thm = store_thm(
  "moduleRead_thm",
  ``!s tk r. (moduleRead P c s = (tk, r)) ==> STRLEN r <= STRLEN s``,
  SIMP_TAC (srw_ss())[moduleRead_def, LET_THM] THEN REPEAT GEN_TAC THEN
  `?p q. read_while P s [c] = (p,q)`
    by METIS_TAC [TypeBase.nchotomy_of ``:'a # 'b``] THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  `(q = []) \/  ?h t. q = h::t`
    by METIS_TAC [TypeBase.nchotomy_of ``:'a list``]
  THEN1 (SRW_TAC [][] THEN SRW_TAC [][]) THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  `(t = []) \/  ?h2 t2. t = h2::t2`
    by METIS_TAC [TypeBase.nchotomy_of ``:'a list``]
  THEN1 (SRW_TAC [][] THEN SRW_TAC [][] THEN IMP_RES_TAC read_while_thm THEN
         FULL_SIMP_TAC (srw_ss()) []) THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  REVERSE (Cases_on `h = #"."`)
    THEN1 (SRW_TAC [][] THEN SRW_TAC [][] THEN IMP_RES_TAC read_while_thm THEN
           FULL_SIMP_TAC (srw_ss()) []) THEN
  ASM_SIMP_TAC (srw_ss())[] THEN
  Q.MATCH_ABBREV_TAC `option_CASE PP XX YY = (tk,r) ==> RR` THEN
  MAP_EVERY Q.UNABBREV_TAC [`XX`, `YY`, `RR`] THEN
  `PP = NONE ∨ ∃P'. PP = SOME P'`
    by METIS_TAC [TypeBase.nchotomy_of ``:'a option``]
  THEN1 (SRW_TAC [][] THEN IMP_RES_TAC read_while_thm THEN
         FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []) THEN
  ASM_SIMP_TAC (srw_ss())[] THEN
  `?n2 rest2. read_while P' t2 [h2] = (n2,rest2)`
    by METIS_TAC [TypeBase.nchotomy_of ``:'a # 'b``] THEN
  SRW_TAC [][] THEN IMP_RES_TAC read_while_thm THEN
  FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [])

val str_to_syms_def = tDefine "str_to_syms" `
  (str_to_syms "" = []) /\
  (str_to_syms (c::str) =
     if isSpace c then (* skip blank space *)
       let (n,rest) = read_while isSpace str [] in
         str_to_syms str else
     if isDigit c then (* read number *)
       let (n,rest) = read_while isDigit str [] in
         NumberS (num_from_dec_string (c::n)) :: str_to_syms rest else
     if isAlpha c then (* read alpha-numeric identifier/keyword *)
       let (n,rest) = moduleRead isAlphaNumPrime c str
       in
         n :: str_to_syms rest else
     if c = #"'" then (* read type variable *)
       let (n,rest) = read_while isAlphaNum str [c]
       in
         OtherS n :: str_to_syms rest else
     if c = #"\"" then (* read string *)
       let (t,rest) = read_string str "" in
         t :: str_to_syms rest else
     if isPREFIX "*)" (c::str) then [ErrorS] else
     if isPREFIX "(*" (c::str) then
       case skip_comment (TL str) 0 of
       | NONE => [ErrorS]
       | SOME rest => str_to_syms rest else
     if is_single_char_symbol c then (* single character tokens *)
       OtherS [c] :: str_to_syms str else
     if isSymbol c then (* read symbol identifier *)
       let (n,rest) = moduleRead isSymbol c str
       in
         n :: str_to_syms rest
     else (* input not recognised *)
       [ErrorS])`
  (WF_REL_TAC `measure LENGTH` THEN REPEAT STRIP_TAC
   THEN IMP_RES_TAC (GSYM moduleRead_thm)
   THEN IMP_RES_TAC (GSYM read_while_thm)
   THEN IMP_RES_TAC (GSYM read_string_thm)
   THEN IMP_RES_TAC skip_comment_thm THEN Cases_on `str`
   THEN FULL_SIMP_TAC (srw_ss()) [LENGTH] THEN DECIDE_TAC)

(*

  EVAL ``str_to_syms "3 (* hi (* there \" *) *) ~4 \" (* *)\" <= ;; "``

*)


val splitAtP_def = Define`
  splitAtP P [] k = k [] [] ∧
  splitAtP P (h::t) k = if P h then k [] (h::t)
                        else splitAtP P t (λp. k (h::p))
`

val moduleSplit_def = Define`
  moduleSplit s =
    splitAtP (λc. c = #".") s
             (λp sfx.
                 case sfx of
                     [] => if isAlpha (HD s) then AlphaT s
                           else SymbolT s
                   | [_] => LexErrorT
                   | _::t => if MEM #"." t then LexErrorT
                             else LongidT p t)
`



val get_token_def = Define `
  get_token s =
    if s = "#" then HashT else
    if s = "(" then LparT else
    if s = ")" then RparT else
    if s = "*" then StarT else
    if s = "," then CommaT else
    if s = "->" then ArrowT else
    if s = "..." then DotsT else
    if s = ":" then ColonT else
    if s = ":>" then SealT else
    if s = ";" then SemicolonT else
    if s = "=" then EqualsT else
    if s = "=>" then DarrowT else
    if s = "[" then LbrackT else
    if s = "]" then RbrackT else
    if s = "_" then UnderbarT else
    if s = "{" then LbraceT else
    if s = "}" then RbraceT else
    if s = "|" then BarT else
    if s = "abstype" then AbstypeT else
    if s = "and" then AndT else
    if s = "andalso" then AndalsoT else
    if s = "as" then AsT else
    if s = "case" then CaseT else
    if s = "datatype" then DatatypeT else
    if s = "do" then DoT else
    if s = "else" then ElseT else
    if s = "end" then EndT else
    if s = "eqtype" then EqtypeT else
    if s = "exception" then ExceptionT else
    if s = "fn" then FnT else
    if s = "fun" then FunT else
    if s = "functor" then FunctorT else
    if s = "handle" then HandleT else
    if s = "if" then IfT else
    if s = "in" then InT else
    if s = "include" then IncludeT else
    if s = "infix" then InfixT else
    if s = "infixr" then InfixrT else
    if s = "let" then LetT else
    if s = "local" then LocalT else
    if s = "nonfix" then NonfixT else
    if s = "of" then OfT else
    if s = "op" then OpT else
    if s = "open" then OpenT else
    if s = "orelse" then OrelseT else
    if s = "raise" then RaiseT else
    if s = "rec" then RecT else
    if s = "sharing" then SharingT else
    if s = "sig" then SigT else
    if s = "signature" then SignatureT else
    if s = "struct" then StructT else
    if s = "structure" then StructureT else
    if s = "then" then ThenT else
    if s = "type" then TypeT else
    if s = "val" then ValT else
    if s = "where" then WhereT else
    if s = "while" then WhileT else
    if s = "with" then WithT else
    if s = "withtype" then WithtypeT else
    if HD s = #"'" then TyvarT s else
    moduleSplit s`;

(*

Warning! The get_token function never maps into any of the following:

  NewlineT
  ZeroT
  WhitespaceT
  DigitT of string
  NumericT of string
  HexintT of string
  WordT of string
  HexwordT of string
  RealT of string
  CharT of string

*)

val syms_to_tokens_def = Define `
  (syms_to_tokens acc [] = acc) /\
  (syms_to_tokens acc (ErrorS::xs) =
     syms_to_tokens (SNOC LexErrorT acc) xs) /\
  (syms_to_tokens acc (StringS s::xs) =
     syms_to_tokens (SNOC (StringT s) acc) xs) /\
  (syms_to_tokens acc (NumberS n::xs) =
     syms_to_tokens (SNOC (IntT (& n)) acc) xs) /\
  (syms_to_tokens acc (OtherS s::xs) =
     syms_to_tokens (SNOC (get_token s) acc) xs)`;

(* top-level lexer specification *)

val lexer_fun_def = Define `
  lexer_fun = syms_to_tokens [] o str_to_syms`;

(*

  EVAL ``lexer_fun "3 (* hi (* there \" *) *) ~4 \" (* *)\" <= ;; "``;
  EVAL ``lexer_fun "a b cd c2 c3'"``;
  EVAL ``lexer_fun "'a 'b '2"``;
  EVAL ``lexer_fun "'"``;
  EVAL ``lexer_fun "x.y +.foo y.+ +.+ foo'.z z.foo' + 3 + x. + .z"``

*)

val _ = export_theory();
