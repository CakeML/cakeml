(*
  A functional specification of lexing from strings to token lists.
*)
Theory lexer_fun
Ancestors
  location string list tokens ASCIInumbers
Libs
  preamble stringLib intLib

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
         | LongS (string list) string (* ["Foo";"Bar"] "<" is Foo.Bar.< *)
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

Definition read_char_as_3digits_def:
  read_char_as_3digits str =
  let ds = TAKE 3 str ;
      rest = DROP 3 str ;
  in
    if LENGTH ds < 3 then NONE
    else
      case FOLDL (λA d. case A of
                          NONE => NONE
                        | SOME A0 => if isDigit d then
                                       SOME (10 * A0 + (ORD d - 48))
                                     else NONE)
                 (SOME 0) ds of
        NONE => NONE
      | SOME ci =>
          if ci < 256 then SOME (CHR ci, rest)
          else NONE
End

Theorem read_char_as_3digits_reduces:
  ∀str0 c str.
    read_char_as_3digits str0 = SOME (c, str) ⇒
    LENGTH str0 = LENGTH str + 3
Proof
  simp[read_char_as_3digits_def, LENGTH_DROP, NOT_LESS, LENGTH_TAKE_EQ,
       AllCaseEqs(), PULL_EXISTS]
QED

Definition read_string_def:
  read_string strng s (loc:locn) =
    if strng = "" then (ErrorS, loc, "") else
    if HD strng = #"\"" then (StringS s, loc, TL strng) else
    if HD strng = #"\n" then (ErrorS, next_line loc, TL strng) else
    if HD strng <> #"\\" then
      read_string (TL strng) (s ++ [HD strng]) (next_loc 1 loc)
    else
      case TL strng of
      | #"\\"::cs => read_string cs (s ++ "\\") (next_loc 2 loc)
      | #"\""::cs => read_string cs (s ++ "\"") (next_loc 2 loc)
      | #"a"::cs => read_string cs (s ++ [CHR 7]) (next_loc 2 loc)
      | #"b"::cs => read_string cs (s ++ [CHR 8]) (next_loc 2 loc)
      | #"t"::cs => read_string cs (s ++ [CHR 9]) (next_loc 2 loc)
      | #"n"::cs => read_string cs (s ++ [CHR 10]) (next_loc 2 loc)
      | #"v"::cs => read_string cs (s ++ [CHR 11]) (next_loc 2 loc)
      | #"f"::cs => read_string cs (s ++ [CHR 12]) (next_loc 2 loc)
      | #"r"::cs => read_string cs (s ++ [CHR 13]) (next_loc 2 loc)
      | c::cs => if isDigit c then
                   case read_char_as_3digits (c::cs) of
                     NONE => (ErrorS, loc, c::cs)
                   | SOME (c, cs') => read_string cs' (s ++ [c])
                                                      (next_loc 4 loc)
                 else (ErrorS, loc, TL strng)
      | _ => (ErrorS, loc, TL strng)
Termination
  WF_REL_TAC `measure (LENGTH o FST)` THEN REPEAT STRIP_TAC THEN
  Cases_on `strng` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  imp_res_tac read_char_as_3digits_reduces >> gs[]
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
  \\ IF_CASES_TAC \\ gvs [SF SFY_ss,ADD1]
  \\ IF_CASES_TAC \\ gvs [SF SFY_ss,ADD1]
  \\ IF_CASES_TAC \\ gvs [SF SFY_ss,ADD1]
  \\ CASE_TAC \\ gvs []
  \\ rpt (IF_CASES_TAC \\ gvs [SF SFY_ss,ADD1]
          >- (rpt strip_tac \\ res_tac \\ gvs []))
  \\ IF_CASES_TAC \\ gvs []
  \\ gvs [AllCaseEqs()] \\ rw [] \\ gvs []
  \\ drule read_char_as_3digits_reduces \\ simp[]
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
  res_tac >> simp[]
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
  res_tac >> simp[]
QED

Definition isAlphaNumPrime_def:
  isAlphaNumPrime c <=> isAlphaNum c \/ (c = #"'") \/ (c = #"_")
End

Definition read_Ident_ret_def:
  read_Ident_ret acc n new_loc rest =
    if NULL acc then
      (OtherS n, new_loc, rest)
    else
      (LongS (REVERSE acc) n, new_loc, rest)
End

Definition read_Ident_def:
  read_Ident [] loc acc = (ErrorS, loc, []) ∧
  read_Ident (c::strng) loc acc =
    if is_single_char_symbol c then (* single character tokens, i.e. delimiters *)
      if NULL acc then
        (OtherS [c], next_loc 1 loc, strng)
      else
        (ErrorS, loc, strng)
    else if isSymbol c then
      let (n,rest) = read_while isSymbol strng [c] in
      let new_loc = next_loc (LENGTH n) loc in
        read_Ident_ret acc n new_loc rest
    else if isAlpha c then
      let (n,rest) = read_while isAlphaNumPrime strng [c] in
      let new_loc = next_loc (LENGTH n) loc in
        case rest of
        | [] => read_Ident_ret acc n new_loc rest
        | c1::rest1 =>
          if c1 = #"." then read_Ident rest1 new_loc (n::acc)
          else read_Ident_ret acc n new_loc rest
    else (* input not recognised *)
      (ErrorS, loc, strng)
Termination
  wf_rel_tac ‘measure (LENGTH o FST)’ \\ rw []
  \\ imp_res_tac (GSYM read_while_thm)
  \\ Cases_on ‘strng’ \\ gvs []
End

(* next_sym reads the next symbol from a string, returning NONE if at eof *)
Definition next_sym_def:
  (next_sym "" _ = NONE) /\
  (next_sym (c::strng) loc =
     if c = #"\n" then (* skip new line *)
        next_sym strng (next_line loc)
     else if isSpace c then (* skip blank space *)
       next_sym strng (next_loc 1 loc)
     else if isDigit c then (* read number *)
       if strng ≠ "" ∧ c = #"0" ∧ HD strng = #"w" then
         if TL strng = "" then SOME (ErrorS, Locs loc loc, "")
         else if isDigit (HD (TL strng)) then
           let (n,rest) = read_while isDigit (TL strng) [] in
             SOME (WordS (num_from_dec_string n),
                   Locs loc (next_loc (LENGTH n + 1) loc),
                   rest)
         else if HD(TL strng) = #"x" then
           let (n,rest) = read_while isHexDigit (TL (TL strng)) [] in
             SOME (WordS (num_from_hex_string n),
                   Locs loc (next_loc (LENGTH n + 2) loc),
                   rest)
         else SOME (ErrorS, Locs loc loc, TL strng)
       else
         if strng ≠ "" ∧ c = #"0" ∧ HD strng = #"x" then
           let (n,rest) = read_while isHexDigit (TL strng) [] in
             SOME (NumberS (& (num_from_hex_string n)),
                   Locs loc (next_loc (LENGTH n) loc),
                   rest)
         else
           let (n,rest) = read_while isDigit strng [] in
             SOME (NumberS (&(num_from_dec_string (c::n))),
                   Locs loc (next_loc (LENGTH n) loc),
                   rest)
     else if c = #"~" /\ strng <> "" /\ isDigit (HD strng) then (* read negative number *)
       let (n,rest) = read_while isDigit strng [] in
         SOME (NumberS (0- &(num_from_dec_string n)),
               Locs loc (next_loc (LENGTH n + 1) loc),
               rest)
     else if c = #"'" then (* read type variable *)
       let (n,rest) = read_while isAlphaNumPrime strng [c] in
         SOME (OtherS n, Locs loc (next_loc (LENGTH n - 1) loc),
               rest)
     else if c = #"\"" then (* read string *)
       let (t, loc', rest) = read_string strng "" (next_loc 1 loc) in
         SOME (t, Locs loc loc', rest)
     else if isPREFIX "*)" (c::strng) then
       SOME (ErrorS, Locs loc (next_loc 2 loc), TL strng)
     else if isPREFIX "#\"" (c::strng) then
       let (t, loc', rest) = read_string (TL strng) "" (next_loc 2 loc) in
         SOME (mkCharS t, Locs loc loc', rest)
     else if isPREFIX "#(" (c::strng) then
       let (t, loc', rest) = read_FFIcall (TL strng) "" (next_loc 2 loc) in
         SOME (t, Locs loc loc', rest)
     else if isPREFIX "(*" (c::strng) then
       case skip_comment (TL strng) 0 (next_loc 2 loc) of
       | NONE => SOME (ErrorS, Locs loc (next_loc 2 loc), "")
       | SOME (rest, loc') => next_sym rest loc'
     else if c = #"_" then SOME (OtherS "_", Locs loc loc, strng)
     else
       let (tok,end_loc,rest) = read_Ident (c::strng) loc [] in
         SOME (tok, Locs loc end_loc, rest))
Termination
  wf_rel_tac ‘measure (LENGTH o FST)’ \\ rw []
  \\ imp_res_tac (GSYM read_while_thm)
  \\ imp_res_tac (GSYM read_string_thm)
  \\ Cases_on ‘strng’ \\ gvs []
  \\ imp_res_tac skip_comment_thm \\ gvs []
End

(* EVAL “next_sym "  Foo.Bar.<  " (POSN 0 0)” *)

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

Theorem read_Ident_LESS:
  ∀xs l acc s loc rest.
    read_Ident xs l acc = (s,loc,rest) ⇒
    if xs = [] then rest = [] else LENGTH rest < LENGTH xs
Proof
  ho_match_mp_tac read_Ident_ind \\ rpt strip_tac
  \\ gvs [read_Ident_def,AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [read_Ident_ret_def,AllCaseEqs()]
  \\ imp_res_tac read_while_thm \\ gvs []
  \\ Cases_on ‘rest1’ \\ gvs []
QED

Theorem next_sym_LESS:
  ∀input l s l' rest.
    next_sym input l = SOME (s, l', rest) ⇒
    LENGTH rest < LENGTH input
Proof
  ho_match_mp_tac next_sym_ind \\ rw []
  >- simp [next_sym_def]
  \\ pop_assum mp_tac
  \\ simp [next_sym_def,AllCaseEqs()]
  \\ rpt strip_tac \\ gvs []
  \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac skip_comment_thm \\ simp[]
  \\ imp_res_tac read_while_thm \\ gvs []
  \\ imp_res_tac read_string_thm \\ gvs []
  \\ imp_res_tac read_FFIcall_reduces_input \\ gvs []
  \\ imp_res_tac read_Ident_LESS \\ gvs []
  \\ Cases_on ‘input’ \\ gvs []
  \\ Cases_on ‘t’ \\ gvs []
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
             AlphaT (implode (c::s))
           else
             SymbolT (implode (c::s))
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
    if s <> "" /\ HD s = #"'" then TyvarT (implode s) else
    processIdent s
End

Definition to_path_def:
  to_path [] = End ∧
  to_path (x::xs) = Mod x (to_path xs)
End

Definition token_of_sym_def:
  token_of_sym s =
    case s of
    | ErrorS    => LexErrorT
    | StringS s => StringT (implode s)
    | CharS c => CharT c
    | NumberS i => IntT i
    | WordS n => WordT n
    | LongS xs s => LongidT (to_path (MAP implode xs)) (implode s)
    | FFIS s => FFIT (implode s)
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
