(*
  A functional specification of lexing from strings to token lists.
*)
open HolKernel Parse boolLib bossLib;

val _ = new_theory "lexer_fun";

open preamble locationTheory;
open stringTheory stringLib listTheory tokensTheory ASCIInumbersTheory intLib;

(* This script defines the functional spec for the assembly
   implementation of the lexer. This lexer specification consists of
   two phases. The first phase reads a string and returns a list of
   symbols. The second phase converts the symbol list into a list of
   tokens. The implementation merges these two phases. *)

(* intermediate symbols *)

Datatype:
  symbol = StringS string
         | CharS char
         | NumberS int
         | WordS num
         | LongS string (* identifiers with a . in them *)
         | FFIS string
         | OtherS string
         | ErrorS
End

(* helper functions *)
Definition mkCharS_def:
  (mkCharS (StringS s) = if LENGTH s = 1 then CharS (HD s)
                         else ErrorS) /\
  (mkCharS _ = ErrorS)
End

Definition read_while_def:
  (read_while P "" s = (IMPLODE (REVERSE s),"")) /\
  (read_while P (STRING c cs) s =
     if P c then read_while P cs (c :: s)
            else (IMPLODE (REVERSE s),STRING c cs))
End

Theorem read_while_thm:
   ∀cs s cs' s'.
       (read_while P cs s = (s',cs')) ⇒ STRLEN cs' <= STRLEN cs
Proof
  Induct THEN SRW_TAC [][read_while_def] THEN SRW_TAC [][] THEN
  RES_TAC THEN FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND] THEN DECIDE_TAC
QED

Definition is_single_char_symbol_def:
  is_single_char_symbol c = MEM c "()[]{},;"
End

Definition isSymbol_def:
  isSymbol c = MEM c (CHR 96 (* backquote *) :: "!%&$#+-/:<=>?@\\~^|*")
End

Definition next_loc_def:
  next_loc n (POSN r c) = POSN r (c+n) ∧
  next_loc n x = x
End

Definition next_line_def:
  next_line (POSN r c) = POSN (r+1) 0 ∧
  next_line x = x
End

Definition read_string_def:
  read_string str s (loc:locn) =
    if str = "" then (ErrorS, loc, "") else
    if HD str = #"\"" then (StringS s, loc, TL str) else
    if HD str = #"\n" then (ErrorS, next_line loc, TL str) else
    if HD str <> #"\\" then
      read_string (TL str) (s ++ [HD str]) (next_loc 1 loc)
    else
      case TL str of
      | #"\\"::cs => read_string cs (s ++ "\\") (next_loc 2 loc)
      | #"\""::cs => read_string cs (s ++ "\"") (next_loc 2 loc)
      | #"n"::cs => read_string cs (s ++ "\n") (next_loc 2 loc)
      | #"t"::cs => read_string cs (s ++ "\t") (next_loc 2 loc)
      | _ => (ErrorS, loc, TL str)
Termination
  WF_REL_TAC `measure (LENGTH o FST)` THEN REPEAT STRIP_TAC
  THEN Cases_on `str` THEN FULL_SIMP_TAC (srw_ss()) [] THEN DECIDE_TAC
End

Theorem read_string_thm:
  ∀s t l l' x1 x2. (read_string s t l = (x1, l', x2)) ⇒
                   (LENGTH x2 <= LENGTH s + LENGTH t)
Proof
  ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ HO_MATCH_MP_TAC (fetch "-" "read_string_ind")
  \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [read_string_def]
  \\ Cases_on `s` \\ SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] [LENGTH] \\ RES_TAC \\ TRY DECIDE_TAC
  \\ SRW_TAC [] [LENGTH] \\ Cases_on `t'`
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ CCONTR_TAC
  \\ Q.PAT_X_ASSUM `(x1, l', x2) = xxx` MP_TAC
  \\ SIMP_TAC std_ss [] \\ SRW_TAC [] []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ RES_TAC \\ TRY DECIDE_TAC \\ CCONTR_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH] \\ DECIDE_TAC
QED

Definition skip_comment_def:
  (skip_comment "" d _ = NONE) /\
  (skip_comment [x] d _ = NONE) /\
  (skip_comment (x::y::xs) d loc =
    if [x;y] = "(*" then
      skip_comment xs (d+1:num) (next_loc 2 loc)
    else if [x;y] = "*)" then
      (if d = 0 then SOME (xs, next_loc 2 loc)
       else skip_comment xs (d-1) (next_loc 2 loc))
    else if ORD x = 10 then
      skip_comment (y::xs) d (next_line loc)
    else skip_comment (y::xs) d (next_loc 1 loc))
End

Theorem skip_comment_thm:
   ∀xs d l l' str. (skip_comment xs d l = SOME (str, l')) ⇒ LENGTH str <= LENGTH xs
Proof
  ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ HO_MATCH_MP_TAC (fetch "-" "skip_comment_ind") \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [skip_comment_def]
  \\ SRW_TAC [] [] \\ RES_TAC \\ TRY DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ SRW_TAC [] [] \\ RES_TAC
  \\ DECIDE_TAC
QED

Definition read_FFIcall_def:
  (read_FFIcall "" acc loc = (ErrorS, loc, "")) ∧
  (read_FFIcall (c::s0) acc loc =
      if c = #")" then
        (FFIS (REVERSE acc), next_loc 2 loc, s0)
      else if c = #"\n" then (ErrorS, loc, s0)
      else if isSpace c then
        read_FFIcall s0 acc (next_loc 1 loc)
      else
        read_FFIcall s0 (c::acc) (next_loc 1 loc))
End

Theorem read_FFIcall_reduces_input:
   ∀s0 a l0 t l s.
     read_FFIcall s0 a l0 = (t, l, s) ⇒ LENGTH s < LENGTH s0 + 1
Proof
  Induct >> dsimp[read_FFIcall_def, bool_case_eq] >> rw[] >>
  qpat_x_assum `_ = _` (assume_tac o SYM) >> res_tac >> simp[]
QED

Definition read_REPLcommand_def:
  (read_REPLcommand "" acc loc = (ErrorS, loc, "")) ∧
  (read_REPLcommand (c::s0) acc loc =
      if c = #"}" then
        (FFIS (REVERSE acc), loc with col updated_by (+) 2, s0)
      else if c = #"\n" then (ErrorS, loc, s0)
      else if isSpace c then
        read_REPLcommand s0 acc (loc with col updated_by (+) 1)
      else
        read_REPLcommand s0 (c::acc) (loc with col updated_by (+) 1))
End

Theorem read_REPLcommand_reduces_input:
  ∀s0 a l0 t l s.
    read_REPLcommand s0 a l0 = (t, l, s) ⇒ LENGTH s < LENGTH s0 + 1
Proof
  Induct >> dsimp[read_REPLcommand_def, bool_case_eq] >> rw[] >>
  qpat_x_assum `_ = _` (assume_tac o SYM) >> res_tac >> simp[]
QED

Definition isAlphaNumPrime_def:
  isAlphaNumPrime c <=> isAlphaNum c \/ (c = #"'") \/ (c = #"_")
End

(* next_sym reads the next symbol from a string, returning NONE if at eof *)
Definition next_sym_def:
  (next_sym "" _ = NONE) /\
  (next_sym (c::str) loc =
     if c = #"\n" then (* skip new line *)
        next_sym str (next_line loc)
     else if isSpace c then (* skip blank space *)
       next_sym str (next_loc 1 loc)
     else if isDigit c then (* read number *)
       if str ≠ "" ∧ c = #"0" ∧ HD str = #"w" then
         if TL str = "" then SOME (ErrorS, Locs loc loc, "")
         else if isDigit (HD (TL str)) then
           let (n,rest) = read_while isDigit (TL str) [] in
             SOME (WordS (num_from_dec_string n),
                   Locs loc (next_loc (LENGTH n + 1) loc),
                   rest)
         else if HD(TL str) = #"x" then
           let (n,rest) = read_while isHexDigit (TL (TL str)) [] in
             SOME (WordS (num_from_hex_string n),
                   Locs loc (next_loc (LENGTH n + 2) loc),
                   rest)
         else SOME (ErrorS, Locs loc loc, TL str)
       else
         if str ≠ "" ∧ c = #"0" ∧ HD str = #"x" then
           let (n,rest) = read_while isHexDigit (TL str) [] in
             SOME (NumberS (& (num_from_hex_string n)),
                   Locs loc (next_loc (LENGTH n) loc),
                   rest)
         else
           let (n,rest) = read_while isDigit str [] in
             SOME (NumberS (&(num_from_dec_string (c::n))),
                   Locs loc (next_loc (LENGTH n) loc),
                   rest)
     else if c = #"~" /\ str <> "" /\ isDigit (HD str) then (* read negative number *)
       let (n,rest) = read_while isDigit str [] in
         SOME (NumberS (0- &(num_from_dec_string n)),
               Locs loc (next_loc (LENGTH n) loc),
               rest)
     else if c = #"'" then (* read type variable *)
       let (n,rest) = read_while isAlphaNumPrime str [c] in
         SOME (OtherS n, Locs loc (next_loc (LENGTH n - 1) loc),
               rest)
     else if c = #"\"" then (* read string *)
       let (t, loc', rest) = read_string str "" (next_loc 1 loc) in
         SOME (t, Locs loc loc', rest)
     else if isPREFIX "*)" (c::str) then
       SOME (ErrorS, Locs loc (next_loc 2 loc), TL str)
     else if isPREFIX "#\"" (c::str) then
       let (t, loc', rest) = read_string (TL str) "" (next_loc 2 loc) in
         SOME (mkCharS t, Locs loc loc', rest)
     else if isPREFIX "#(" (c::str) then
       let (t, loc', rest) = read_FFIcall (TL str) "" (next_loc 2 loc) in
         SOME (t, Locs loc loc', rest)
     else if isPREFIX "(*" (c::str) then
       case skip_comment (TL str) 0 (next_loc 2 loc) of
       | NONE => SOME (ErrorS, Locs loc (next_loc 2 loc), "")
       | SOME (rest, loc') => next_sym rest loc'
     else if is_single_char_symbol c then (* single character tokens, i.e. delimiters *)
       SOME (OtherS [c], Locs loc loc, str)
     else if isSymbol c then
       let (n,rest) = read_while isSymbol str [c] in
         SOME (OtherS n, Locs loc (next_loc (LENGTH n - 1) loc),
               rest)
     else if isAlpha c then (* read identifier *)
       let (n,rest) = read_while isAlphaNumPrime str [c] in
         case rest of
              #"."::rest' =>
                (case rest' of
                      c'::rest' =>
                        if isAlpha c' then
                          let (n', rest'') = read_while isAlphaNumPrime rest' [c'] in
                            SOME (LongS (n ++ "." ++ n'),
                                  Locs loc
                                       (next_loc (LENGTH n + LENGTH n') loc),
                                  rest'')
                        else if isSymbol c' then
                          let (n', rest'') = read_while isSymbol rest' [c'] in
                            SOME (LongS (n ++ "." ++ n'),
                                  Locs loc
                                       (next_loc (LENGTH n + LENGTH n') loc),
                                  rest'')
                        else
                          SOME (ErrorS,
                                Locs loc (next_loc (LENGTH n) loc),
                                rest')
                    | "" => SOME (ErrorS,
                                  Locs loc (next_loc (LENGTH n) loc),
                                  []))
            | _ => SOME (OtherS n,
                         Locs loc (next_loc (LENGTH n - 1) loc),
                         rest)
     else if c = #"_" then SOME (OtherS "_", Locs loc loc, str)
     else (* input not recognised *)
       SOME (ErrorS, Locs loc loc, str))
Termination
  WF_REL_TAC `measure (LENGTH o FST) ` THEN REPEAT STRIP_TAC
   THEN IMP_RES_TAC (GSYM read_while_thm)
   THEN IMP_RES_TAC (GSYM read_string_thm)
   THEN IMP_RES_TAC skip_comment_thm THEN Cases_on `str`
   THEN FULL_SIMP_TAC (srw_ss()) [LENGTH] THEN DECIDE_TAC
End

Theorem lem1[local]:
  ((let (x,y) = z a in f x y) = P a) = (let (x,y) = z a in (f x y = P a))
Proof
  EQ_TAC THEN
  SRW_TAC [] [LET_THM] THEN
  Cases_on `z a` THEN
  FULL_SIMP_TAC std_ss []
QED

Theorem lem2[local]:
  ((let (x,y) = z a in f x y) ⇒ P a) = (let (x,y) = z a in (f x y ⇒ P a))
Proof
  EQ_TAC THEN
  SRW_TAC [] [LET_THM] THEN
  Cases_on `z a` THEN
  FULL_SIMP_TAC std_ss []
QED

Theorem read_while_EMPTY[simp] = CONJUNCT1 read_while_def;

Theorem NOT_NIL_EXISTS_CONS[local]:
  (n ≠ [] ⇔ ∃h t. n = h :: t) ∧
  (list_CASE n F P ⇔ ∃h t. n = h :: t ∧ P h t)
Proof Cases_on `n` >> simp[]
QED

val listeq = CaseEq "list"
val optioneq = CaseEq "option"

Theorem next_sym_LESS:
   ∀input l s l' rest.
     (next_sym input l = SOME (s, l', rest)) ⇒ LENGTH rest < LENGTH input
Proof
  ho_match_mp_tac (fetch "-" "next_sym_ind") >>
  simp[next_sym_def, bool_case_eq, listeq, optioneq] >> rw[] >> fs[] >>
  rpt (pairarg_tac >> fs[]) >> rveq >> fs[NOT_NIL_EXISTS_CONS] >>
  rveq >> fs[] >> rveq >> fs[] >>
  MAP_EVERY imp_res_tac [read_while_thm,read_string_thm] >> every_case_tac >>
  fs[listeq, optioneq, bool_case_eq] >> rveq >> fs[] >>
  TRY (rename1 `skip_comment` >>
       res_tac >> imp_res_tac skip_comment_thm >> simp[] >> NO_TAC) >>
  TRY (rename1 `UNCURRY` >>
       rpt (pairarg_tac>> fs[]) >> rveq >>
       imp_res_tac read_while_thm >> simp[] >> NO_TAC) >>
  TRY (rename1 `read_FFIcall` >>
       imp_res_tac read_FFIcall_reduces_input >> simp[] >> NO_TAC) >>
  TRY (rename1 `read_REPLcommand` >>
       imp_res_tac read_REPLcommand_reduces_input >> simp[] >> NO_TAC) >>
  qpat_x_assum ‘SOME _ = next_sym _ _’ (assume_tac o SYM) >>
  first_x_assum drule >> simp[]
QED

Definition init_loc_def:
   init_loc = POSN 0 0
End

(*

  EVAL ``next_sym " (* hi (* there \" *) *)\n  ~4 \" (* *)\" <= ;; " init_loc ``
  EVAL ``next_sym "0w10 +" init_loc``;
  EVAL ``next_sym "0wx1A +" init_loc``;

*)

(* next_token reads the next token from a string *)

Definition processIdent_def:
  processIdent s =
    case s of
       | "" => LexErrorT
       | c::s =>
           if isAlpha c then
             AlphaT (c::s)
           else
             SymbolT (c::s)
End

Definition get_token_def[nocompute]:
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
    if s <> "" /\ HD s = #"'" then TyvarT s else
    processIdent s
End

Definition token_of_sym_def:
  token_of_sym s =
    case s of
    | ErrorS    => LexErrorT
    | StringS s => StringT s
    | CharS c => CharT c
    | NumberS i => IntT i
    | WordS n => WordT n
    | LongS s => let (s1,s2) = SPLITP (\x. x = #".") s in
                   LongidT s1 (case s2 of "" => "" | (c::cs) => cs)
    | FFIS s => FFIT s
    | OtherS s  => get_token s
End

Definition next_token_def:
  next_token input loc =
    case next_sym input loc of
    | NONE => NONE
    | SOME (sym, locs, rest_of_input) =>
        SOME (token_of_sym sym, locs, rest_of_input)
End

Theorem next_token_LESS:
   ∀s l l' rest input. (next_token input l = SOME (s, l', rest)) ⇒
                   LENGTH rest < LENGTH input
Proof
  NTAC 5 STRIP_TAC THEN Cases_on `next_sym input l`
  THEN ASM_SIMP_TAC (srw_ss()) [next_token_def]
  THEN every_case_tac
  THEN ASM_SIMP_TAC (srw_ss()) []
  THEN IMP_RES_TAC next_sym_LESS THEN REPEAT STRIP_TAC
  THEN FULL_SIMP_TAC std_ss []
QED

(* top-level lexer specification *)

Definition lexer_fun_aux_def:
  lexer_fun_aux input loc =
    case next_token input loc of
    | NONE => []
    | SOME (token, Locs loc' loc'', rest_of_input) =>
        (token, Locs loc' loc'') ::
            lexer_fun_aux rest_of_input (next_loc 1 loc'')
Termination
  WF_REL_TAC `measure (LENGTH o FST)` >> rw[] >> imp_res_tac next_token_LESS
End

Definition lexer_fun_def:
  lexer_fun input = lexer_fun_aux input init_loc
End

(*

  A few tests:

    EVAL ``lexer_fun "3 (* hi (* there \" *) *) ~4 \" (* *)\" <= ;; "``;
    EVAL ``lexer_fun "3 (* hi (* there  *) *) ~4 \" (* *)\" <= ;; "``;
    EVAL ``lexer_fun "a b cd c2 c3'"``;
    EVAL ``lexer_fun "'a 'b '2"``;
    EVAL ``lexer_fun "'"``;
    EVAL ``lexer_fun "0w10 + 0wxAa3F"``;
    EVAL ``lexer_fun "0w"`;

*)

(* split a list of tokens at top-level semicolons *)

Definition toplevel_semi_dex_def:
  (toplevel_semi_dex (i:num) (d:num) [] = NONE) /\
  (toplevel_semi_dex i d ((h,l)::t) =
    if h = SemicolonT /\ (d = 0) then SOME (i+1)
    else if h = LetT then toplevel_semi_dex (i + 1) (d + 1) t
    else if h = StructT then toplevel_semi_dex (i + 1) (d + 1) t
    else if h = SigT then toplevel_semi_dex (i + 1) (d + 1) t
    else if h = LparT then toplevel_semi_dex (i + 1) (d + 1) t
    else if h = EndT then toplevel_semi_dex (i + 1) (d - 1) t
    else if h = RparT then toplevel_semi_dex (i + 1) (d - 1) t
    else toplevel_semi_dex (i + 1) d t)
End

Theorem toplevel_semi_dex_non0[local]:
  ∀i d toks j. (toplevel_semi_dex i d toks = SOME j) ⇒ 0 < j
Proof
  induct_on `toks` >>
  fs [toplevel_semi_dex_def] >>
  TRY (Cases_on `d`) >> fs[] >>
  TRY (Cases_on `h`) >> fs[] >>
  TRY (Cases_on `q`) >> fs[toplevel_semi_dex_def] >>
  prove_tac[]
QED

Definition split_top_level_semi_def:
  (split_top_level_semi toks =
   case toplevel_semi_dex 0 0 toks of
   | NONE => []
   | SOME i =>
       TAKE i toks :: split_top_level_semi (DROP i toks))
Termination
  wf_rel_tac `measure LENGTH` >>
  rw [] >>
  cases_on `toks` >>
  fs [toplevel_semi_dex_def] >>
  cases_on `h` >>
  fs [] >>
  metis_tac [toplevel_semi_dex_non0, DECIDE ``0 < 1:num``, DECIDE ``∀x:num. 0 < x + 1``]
End

val _ = export_theory();
