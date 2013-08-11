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
                             | NumberS of int
                             | LongS of string => string
                             | OtherS of string
                             | ErrorS `;

(* helper functions *)

val read_while_def = Define `
  (read_while P "" s = (IMPLODE (REVERSE s),"")) /\
  (read_while P (STRING c cs) s =
     if P c then read_while P cs (c :: s)
            else (IMPLODE (REVERSE s),STRING c cs))`;

val is_single_char_symbol_def = Define `
  is_single_char_symbol c = MEM c "()[]{},;"`;

val isSymbol_def = Define `
  isSymbol c = MEM c (CHR 96 :: "!%&$#+-/:<=>?@\\~^|*")`;

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
  isAlphaNumPrime c <=> isAlphaNum c \/ c = #"'" ∨ c = #"_"
`

(*
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
  *)

val next_sym_def = tDefine "next_sym" `
  (next_sym "" = NONE) /\
  (next_sym (c::str) =
     if isSpace c then (* skip blank space *)
       next_sym str
     else if isDigit c then (* read number *)
       let (n,rest) = read_while isDigit str [] in
         SOME (NumberS (&(num_from_dec_string (c::n))), rest)
     else if c = #"~" ∧ str ≠ "" ∧ isDigit (HD str) then (* read negative number *)
       let (n,rest) = read_while isDigit str [] in
         SOME (NumberS (0- &(num_from_dec_string n)), rest)
     else if c = #"'" then (* read type variable *)
       let (n,rest) = read_while isAlphaNumPrime str [c] in
         SOME (OtherS n, rest)
     else if c = #"\"" then (* read string *)
       let (t,rest) = read_string str "" in
         SOME (t, rest)
     else if isPREFIX "*)" (c::str) then
       SOME (ErrorS, TL str)
     else if isPREFIX "(*" (c::str) then
       case skip_comment (TL str) 0 of
       | NONE => SOME (ErrorS, "")
       | SOME rest => next_sym rest
     else if is_single_char_symbol c then (* single character tokens, i.e. delimiters *)
       SOME (OtherS [c], str)
     else if isSymbol c then
       let (n,rest) = read_while isSymbol str [c] in
         SOME (OtherS n, rest)
     else if isAlpha c then (* read identifier *)
       let (n,rest) = read_while isAlphaNumPrime str [c] in
         case rest of
              #"."::c'::rest' =>
                if isAlpha c' then
                  let (n', rest'') = read_while isAlphaNumPrime rest' [c'] in
                    SOME (LongS n n', rest'')
                else if isSymbol c' then
                  let (n', rest'') = read_while isSymbol rest' [c'] in
                    SOME (LongS n n', rest'')
                else
                    SOME (ErrorS, rest')
            | _ => SOME (OtherS n, rest)
     else if c = #"_" then SOME (OtherS "_", str)
     else (* input not recognised *)
       SOME (ErrorS, str))`
  (WF_REL_TAC `measure LENGTH` THEN REPEAT STRIP_TAC
   THEN IMP_RES_TAC (GSYM read_while_thm)
   THEN IMP_RES_TAC (GSYM read_string_thm)
   THEN IMP_RES_TAC skip_comment_thm THEN Cases_on `str`
   THEN FULL_SIMP_TAC (srw_ss()) [LENGTH] THEN DECIDE_TAC);

val lem1 = Q.prove (
`((let (x,y) = z a in f x y) = P a) = (let (x,y) = z a in (f x y = P a))`,
EQ_TAC THEN
SRW_TAC [] [LET_THM] THEN
Cases_on `z a` THEN
FULL_SIMP_TAC std_ss []);

val lem2 = Q.prove (
`((let (x,y) = z a in f x y) ⇒ P a) = (let (x,y) = z a in (f x y ⇒ P a))`,
EQ_TAC THEN
SRW_TAC [] [LET_THM] THEN
Cases_on `z a` THEN
FULL_SIMP_TAC std_ss []);

val next_sym_LESS = prove(
  ``!input. (next_sym input = SOME (s,rest)) ==> LENGTH rest < LENGTH input``,
  HO_MATCH_MP_TAC (fetch "-" "next_sym_ind") THEN REPEAT STRIP_TAC
  THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [next_sym_def]
  THEN SIMP_TAC (srw_ss()) [METIS_PROVE [] ``(b ==> c) <=> ~b \/ c``]
  THEN SRW_TAC [] [] THEN IMP_RES_TAC read_while_thm
  THEN IMP_RES_TAC read_string_thm
  THEN Cases_on `input` THEN FULL_SIMP_TAC (srw_ss()) []
  THEN SIMP_TAC pure_ss [METIS_PROVE [] ``~b \/ ~c <=> ~(b /\ c:bool)``]
  THEN SIMP_TAC pure_ss [METIS_PROVE [] ``~b \/ c <=> (b ==> c)``]
  THEN REPEAT STRIP_TAC
  THEN TRY (POP_ASSUM MP_TAC THEN Q.PAT_ABBREV_TAC `pat = skip_comment ttt 0`
    THEN Cases_on `pat` THEN FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def])
  THEN REPEAT STRIP_TAC THEN IMP_RES_TAC (GSYM skip_comment_thm)
  THEN FULL_SIMP_TAC (srw_ss()) [LENGTH]
  THEN TRY (Q.PAT_ASSUM `xx = rest` (ASSUME_TAC o GSYM))
  THEN FULL_SIMP_TAC (std_ss++ARITH_ss) [LENGTH]
  THEN Cases_on `rest'`
  THEN FULL_SIMP_TAC (srw_ss()) []
  THEN SRW_TAC [] []
  THEN Cases_on `h' = #"."` 
  THEN SRW_TAC [] []
  THEN FULL_SIMP_TAC (srw_ss()) []
  THEN SRW_TAC [] []
  THEN FULL_SIMP_TAC (std_ss++ARITH_ss) []
  THEN Cases_on `t'`
  THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) []
  THEN SRW_TAC [] []
  THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [lem1]
  THEN POP_ASSUM MP_TAC
  THEN SRW_TAC [] [lem2] 
  THEN IMP_RES_TAC read_while_thm
  THEN BasicProvers.EVERY_CASE_TAC
  THEN FULL_SIMP_TAC (std_ss++ARITH_ss) [LENGTH] 
  THEN SRW_TAC [] []
  THEN FULL_SIMP_TAC (std_ss++ARITH_ss) [LENGTH]);


(*

  EVAL ``next_sym "3 (* hi (* there \" *) *) ~4 \" (* *)\" <= ;; "``
  EVAL ``next_sym " (* hi (* there \" *) *) ~4 \" (* *)\" <= ;; "``

*)

(*
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
*)

val processIdent_def = Define `
  processIdent s =
    case s of
       | "" => LexErrorT
       | #"'"::_ => LexErrorT
       | c::s =>
           if isAlphaNum c then
             if EVERY isAlphaNumPrime s then
               AlphaT (c::s)
             else
               LexErrorT
           else if EVERY isSymbol (c::s) then
             SymbolT (c::s)
           else
             LexErrorT`;

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
    if s = "and" then AndT else
    if s = "andalso" then AndalsoT else
    if s = "as" then AsT else
    if s = "case" then CaseT else
    if s = "datatype" then DatatypeT else
    if s = "else" then ElseT else
    if s = "end" then EndT else
    if s = "eqtype" then EqtypeT else
    if s = "exception" then ExceptionT else
    if s = "fn" then FnT else
    if s = "fun" then FunT else
    if s = "handle" then HandleT else
    if s = "if" then IfT else
    if s = "in" then InT else
    if s = "include" then IncludeT else
    if s = "let" then LetT else
    if s = "local" then LocalT else
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
    if s = "with" then WithT else
    if s = "withtype" then WithtypeT else
    if HD s = #"'" then TyvarT s else
    processIdent s`;

val token_of_sym_def = Define `
  token_of_sym s =
    case s of
    | ErrorS    => LexErrorT
    | StringS s => StringT s
    | NumberS i => IntT i 
    | LongS s1 s2 => LongidT s1 s2
    | OtherS s  => get_token s `;

val next_token_def = Define `
  next_token input =
    case next_sym input of
    | NONE => NONE
    | SOME (sym, rest_of_input) => SOME (token_of_sym sym, rest_of_input)`;

val next_token_LESS = store_thm("next_token_LESS",
  ``!s rest input. (next_token input = SOME (s,rest)) ==>
                   LENGTH rest < LENGTH input``,
  NTAC 3 STRIP_TAC THEN Cases_on `next_sym input`
  THEN ASM_SIMP_TAC (srw_ss()) [next_token_def]
  THEN Cases_on `x` THEN ASM_SIMP_TAC (srw_ss()) []
  THEN IMP_RES_TAC next_sym_LESS THEN REPEAT STRIP_TAC
  THEN FULL_SIMP_TAC std_ss []);

(* top-level lexer specification *)

val tac = WF_REL_TAC `measure LENGTH` THEN SRW_TAC [] [next_token_LESS];

val lexer_fun_def = tDefine "lexer_fun" `
  lexer_fun input =
    case next_token input of
    | NONE => []
    | SOME (token, rest_of_input) => token :: lexer_fun rest_of_input ` tac;

(*

  A few tests:

    EVAL ``lexer_fun "3 (* hi (* there \" *) *) ~4 \" (* *)\" <= ;; "``;
    EVAL ``lexer_fun "a b cd c2 c3'"``;
    EVAL ``lexer_fun "'a 'b '2"``;
    EVAL ``lexer_fun "'"``

*)

(*

  TODO: Should the token datatype be cleaned? A lot of tokens aren't
        produced, e.g. NewlineT, ZeroT, DigitT, NumericT, HexintT,
        WordT, HexwordT, RealT, CharT, TyvarT, LongidT.

*)

val _ = Hol_datatype`semihider = SH_END | SH_PAR`
(* extend with SH_BRACE and SH_BRACKET when records and lists
   are part of the syntax *)

val toplevel_semi_dex_def = Define`
  toplevel_semi_dex (i:num) error stk [] = NONE ∧
  toplevel_semi_dex i error stk (h::t) =
    if h = SemicolonT ∧ (stk = [] ∨ error) then SOME (i+1)
    else if error then toplevel_semi_dex (i + 1) error stk t
    else if h = LetT then toplevel_semi_dex (i + 1) F (SH_END::stk) t
    else if h = StructT then toplevel_semi_dex (i + 1) F (SH_END::stk) t
    else if h = SigT then toplevel_semi_dex (i + 1) F (SH_END::stk) t
    else if h = LparT then toplevel_semi_dex (i + 1) F (SH_PAR::stk) t
    else if h = EndT then
      case stk of
          SH_END :: stk' => toplevel_semi_dex (i + 1) F stk' t
        | _ => toplevel_semi_dex (i + 1) T [] t
    else if h = RparT then
      case stk of
          SH_PAR :: stk' => toplevel_semi_dex (i + 1) F stk' t
        | _ => toplevel_semi_dex (i + 1) T [] t
    else toplevel_semi_dex (i + 1) F stk t
`

(* open lexer_funTheory;
assert
  (aconv ``SOME 16n`` o rhs o concl)
  (EVAL
    ``toplevel_semi_dex 1 F []
        (lexer_fun "let val x = 3; val y = 10 in x + y end; (")``);

assert
  (aconv ``SOME 16n`` o rhs o concl)
  (EVAL
    ``toplevel_semi_dex 1 F []
        (lexer_fun "let val x) = 3; val y = 10 in x + y end; (")``)

*)



val _ = export_theory();
