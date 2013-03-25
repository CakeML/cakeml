open HolKernel Parse boolLib bossLib;

val _ = new_theory "lexer_fun";

open stringTheory stringLib listTheory TokensTheory intLib;

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
  (read_while P "" s = (s,"")) /\
  (read_while P (STRING c cs) s =
     if P c then read_while P cs (STRCAT s (STRING c ""))
            else (s,STRING c cs))`;

val is_single_char_symbol_def = Define `
  is_single_char_symbol c = MEM c "()[];~"`;

val str_to_num_def = Define `
  (str_to_num "" = 0:num) /\
  (str_to_num (STRING c s) = (ORD c - ORD #"0") * 10 ** (LENGTH s) + str_to_num s)`;

val isSymbol_def = Define `
  isSymbol c = (~(isSpace c) /\ ~(isDigit c) /\ ~(isAlpha c) /\
                ~(MEM c "()[];") /\ (ORD #" " < ORD c))`;

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
       (read_while P cs s = (s',cs')) ==> LENGTH cs' <= LENGTH cs + LENGTH s``,
  Induct THEN SIMP_TAC std_ss [read_while_def] THEN REPEAT STRIP_TAC
  THEN Cases_on `P h` THEN FULL_SIMP_TAC std_ss [LENGTH]
  THEN RES_TAC THEN FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND]
  THEN REPEAT (Q.PAT_ASSUM `STRING c cs = cs'` (ASSUME_TAC o GSYM))
  THEN FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND] THEN DECIDE_TAC);

val str_to_syms_def = tDefine "str_to_syms" `
  (str_to_syms "" = []) /\
  (str_to_syms (c::str) =
     if isSpace c then (* skip blank space *)
       str_to_syms str else
     if isDigit c then (* read number *)
       let (n,rest) = read_while isDigit str "" in
         NumberS (str_to_num (c::n)) :: str_to_syms rest else
     if isAlpha c then (* read alpha-numeric identifier/keyword *)
       let (n,rest) = read_while isAlphaNum str "" in
         OtherS (c::n) :: str_to_syms rest else
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
       let (n,rest) = read_while isSymbol str "" in
         OtherS (c::n) :: str_to_syms rest
     else (* input not recognised *)
       [ErrorS])`
  (WF_REL_TAC `measure LENGTH` THEN REPEAT STRIP_TAC
   THEN IMP_RES_TAC (GSYM read_while_thm)
   THEN IMP_RES_TAC (GSYM read_string_thm)
   THEN IMP_RES_TAC skip_comment_thm THEN Cases_on `str`
   THEN FULL_SIMP_TAC (srw_ss()) [LENGTH] THEN DECIDE_TAC)

(*

  EVAL ``str_to_syms "3 (* hi (* there \" *) *) ~4 \" (* *)\" <= ;; "``

*)

val get_token_def = Define `
  get_token s =
    if s = "#" then SOME HashT else
    if s = "(" then SOME LparT else
    if s = ")" then SOME RparT else
    if s = "*" then SOME StarT else
    if s = "," then SOME CommaT else
    if s = "->" then SOME ArrowT else
    if s = "???" then SOME DotsT else     (* no idea *)
    if s = ":" then SOME ColonT else
    if s = "???" then SOME SealT else     (* no idea *)
    if s = ";" then SOME SemicolonT else
    if s = "=" then SOME EqualsT else
    if s = "???" then SOME DarrowT else   (* no idea *)
    if s = "[" then SOME LbrackT else
    if s = "]" then SOME RbrackT else
    if s = "_" then SOME UnderbarT else
    if s = "{" then SOME LbraceT else
    if s = "}" then SOME RbraceT else
    if s = "-" then SOME BarT else
    if s = "abstype" then SOME AbstypeT else
    if s = "and" then SOME AndT else
    if s = "andalso" then SOME AndalsoT else
    if s = "as" then SOME AsT else
    if s = "case" then SOME CaseT else
    if s = "datatype" then SOME DatatypeT else
    if s = "do" then SOME DoT else
    if s = "else" then SOME ElseT else
    if s = "end" then SOME EndT else
    if s = "eqtype" then SOME EqtypeT else
    if s = "exception" then SOME ExceptionT else
    if s = "fn" then SOME FnT else
    if s = "fun" then SOME FunT else
    if s = "functor" then SOME FunctorT else
    if s = "handle" then SOME HandleT else
    if s = "if" then SOME IfT else
    if s = "in" then SOME InT else
    if s = "inlcude" then SOME IncludeT else
    if s = "infix" then SOME InfixT else
    if s = "infixr" then SOME InfixrT else
    if s = "let" then SOME LetT else
    if s = "local" then SOME LocalT else
    if s = "nonfix" then SOME NonfixT else
    if s = "of" then SOME OfT else
    if s = "op" then SOME OpT else
    if s = "open" then SOME OpenT else
    if s = "orelse" then SOME OrelseT else
    if s = "raise" then SOME RaiseT else
    if s = "rec" then SOME RecT else
    if s = "sharing" then SOME SharingT else
    if s = "sig" then SOME SigT else
    if s = "signature" then SOME SignatureT else
    if s = "struct" then SOME StructT else
    if s = "structure" then SOME StructureT else
    if s = "then" then SOME ThenT else
    if s = "type" then SOME TypeT else
    if s = "val" then SOME ValT else
    if s = "where" then SOME WhereT else
    if s = "while" then SOME WhileT else
    if s = "with" then SOME WithT else
    if s = "withtype" then SOME WithtypeT else
      SOME (SymbolT s)`

(*

Warning! The get_token function never maps into any of the following:

  ZeroT
  DigitT of string
  NumericT of string
  HexintT of string
  WordT of string
  HexwordT of string
  RealT of string
  CharT of string
  TyvarT of string
  AlphaT of string
  LongidT of string

*)

val syms_to_tokens_def = Define `
  (syms_to_tokens acc [] = SOME acc) /\
  (syms_to_tokens acc (ErrorS::xs) = NONE) /\
  (syms_to_tokens acc (StringS s::xs) =
   syms_to_tokens (SNOC (StringT s) acc) xs) /\
  (syms_to_tokens acc (NumberS n::xs) =
   syms_to_tokens (SNOC (IntT (& n)) acc) xs) /\
  (syms_to_tokens acc (OtherS s::xs) =
     case get_token s of
     | NONE => NONE
     | SOME t => syms_to_tokens (SNOC t acc) xs)`;

(* top-level lexer specification *)

val lexer_fun_def = Define `
  lexer_fun = syms_to_tokens [] o str_to_syms`;

(*

  EVAL ``lexer_fun "3 (* hi (* there \" *) *) ~4 \" (* *)\" <= ;; "``

*)

val _ = export_theory();
