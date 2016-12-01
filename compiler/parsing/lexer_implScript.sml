open HolKernel Parse boolLib bossLib lcsymtacs;

val _ = new_theory "lexer_impl";

open stringTheory stringLib listTheory tokensTheory lexer_funTheory;

val tac =
 full_simp_tac (srw_ss()) [char_le_def, char_lt_def] >>
 Cases_on `t` >>
 rw [get_token_def, processIdent_def, isAlphaNum_def, isAlpha_def, isDigit_def,
     isLower_def, isUpper_def];

val get_token_eqn = Q.store_thm ("get_token_eqn",
`!s.
  get_token s =
    case s of
         [] => LexErrorT
       | [c] =>
           if c ≤ #";" then
             if c ≤ #")" then
               if c ≤ #"'" then
                 if c = #"#" then HashT else
                 if c = #"'" then TyvarT s else
                 SymbolT s
               else
                 if c = #"(" then LparT else
                 if c = #")" then RparT else
                 SymbolT s
             else
               if c ≤ #"," then
                 if c = #"*" then StarT else
                 if c = #"," then CommaT else
                 SymbolT s
               else
                 if c = #":" then ColonT else
                 if c = #";" then SemicolonT else
                 SymbolT s
           else
             if c ≤ #"]" then
               if c ≤ #"Z" then
                 if #"A" ≤ c ∧ c ≤ #"Z" then AlphaT s else
                 if c = #"=" then EqualsT else
                 SymbolT s
               else
                 if c = #"[" then LbrackT else
                 if c = #"]" then RbrackT else
                 SymbolT s
             else
               if c ≤ #"{" then
                 if c = #"_" then UnderbarT else
                 if #"a" ≤ c ∧ c ≤ #"z" then AlphaT s else
                 if c = #"{" then LbraceT else
                 SymbolT s
               else
                 if c = #"|" then BarT else
                 if c = #"}" then RbraceT else
                 SymbolT s
       | c::s' =>
           if c < #"a" then
             if c ≤ #"." then
               if c = #"'" then TyvarT s else
               if s = "->" then ArrowT else
               if s = "..." then DotsT else
               SymbolT s
             else
               if s = ":>" then SealT else
               if s = "=>" then DarrowT else
               if #"A" ≤ c ∧ c ≤ #"Z" then AlphaT s else
               SymbolT s
           else if c ≤ #"z" then
             if c ≤ #"i" then
               if c ≤ #"e" then
                 if c < #"e" then
                   if s = "and" then AndT else
                   if s = "andalso" then AndalsoT else
                   if s = "as" then AsT else
                   if s = "case" then CaseT else
                   if s = "datatype" then DatatypeT else
                   AlphaT s
                 else
                   if s = "else" then ElseT else
                   if s = "end" then EndT else
                   if s = "eqtype" then EqtypeT else
                   if s = "exception" then ExceptionT else
                   AlphaT s
               else
                 if c ≤ #"h" then
                   if s = "fn" then FnT else
                   if s = "fun" then FunT else
                   if s = "handle" then HandleT else
                   AlphaT s
                 else
                   if s = "if" then IfT else
                   if s = "in" then InT else
                   if s = "include" then IncludeT else
                   AlphaT s
             else
               if c ≤ #"r" then
                 if c = #"l" then
                   if s = "let" then LetT else
                   if s = "local" then LocalT else
                   AlphaT s
                 else if c = #"o" then
                   if s = "of" then OfT else
                   if s = "op" then OpT else
                   if s = "open" then OpenT else
                   if s = "orelse" then OrelseT else
                   AlphaT s
                 else
                   if s = "raise" then RaiseT else
                   if s = "rec" then RecT else
                   AlphaT s
               else
                 if c = #"s" then
                   if s = "sharing" then SharingT else
                   if s = "sig" then SigT else
                   if s = "signature" then SignatureT else
                   if s = "struct" then StructT else
                   if s = "structure" then StructureT else
                   AlphaT s
                 else if c < #"w" then
                   if s = "then" then ThenT else
                   if s = "type" then TypeT else
                   if s = "val" then ValT else
                   AlphaT s
                 else
                   if s = "where" then WhereT else
                   if s = "with" then WithT else
                   if s = "withtype" then WithtypeT else
                   AlphaT s
           else
             SymbolT s`,
 strip_tac >>
 Cases_on `s` >>
 simp_tac (srw_ss()) []
 >- srw_tac [] [processIdent_def, get_token_def] >>
 MAP_EVERY (fn c =>
               Cases_on `h = ^c` >-
               tac >>
               full_simp_tac (srw_ss()) [])
           [``#"a"``, ``#"c"``, ``#"d"``, ``#"e"``, ``#"f"``, ``#"h"``,
            ``#"i"``, ``#"l"``, ``#"o"``, ``#"r"``, ``#"s"``, ``#"t"``, ``#"w"``,
            ``#"v"``, ``#"'"``, ``#"."``, ``#":"``, ``#"-"``, ``#"="``, ``#"#"``,
            ``#"("``, ``#")"``, ``#"*"``, ``#","``, ``#";"``, ``#"|"``, ``#"["``,
            ``#"]"``, ``#"_"``, ``#"{"``, ``#"}"``] >>
 full_simp_tac (srw_ss()) [get_token_def] >>
 rw [processIdent_def, isAlphaNum_def, isAlpha_def, isDigit_def,
     isLower_def, isUpper_def] >>
 full_simp_tac (srw_ss()++ARITH_ss) [char_le_def, char_lt_def] >>
 Cases_on `t` >>
 rw []);

val _ = computeLib.add_persistent_funs(["get_token_eqn"]);

val unhex_alt_def = Define`
  unhex_alt x = (if isHexDigit x then UNHEX x else 0n)`

val num_from_dec_string_alt_def = Define `num_from_dec_string_alt = s2n 10 unhex_alt`;
val num_from_hex_string_alt_def = Define `num_from_hex_string_alt = s2n 16 unhex_alt`;

val next_sym_alt_def = tDefine "next_sym_alt"`
  (next_sym_alt "" = NONE) /\
  (next_sym_alt (c::str) =
     if isSpace c then (* skip blank space *)
       next_sym_alt str
     else if isDigit c then (* read number *)
       if str ≠ "" ∧ c = #"0" ∧ HD str = #"w" then
         if TL str = "" then SOME (ErrorS, "")
         else if isDigit (HD (TL str)) then
           let (n,rest) = read_while isDigit (TL str) []
           in
             SOME (WordS (&num_from_dec_string_alt n), rest)
         else if HD (TL str) = #"x" then
           let (n,rest) = read_while isHexDigit (TL (TL str)) []
           in
             SOME (WordS (&num_from_hex_string_alt n), rest)
         else SOME (ErrorS, TL str)
       else
         let (n,rest) = read_while isDigit str []
         in
           SOME (NumberS (&(num_from_dec_string_alt (c::n))), rest)
     else if c = #"~" /\ str <> "" /\ isDigit (HD str) then (* read negative number *)
       let (n,rest) = read_while isDigit str [] in
         SOME (NumberS (0- &(num_from_dec_string_alt n)), rest)
     else if c = #"'" then (* read type variable *)
       let (n,rest) = read_while isAlphaNumPrime str [c] in
         SOME (OtherS n, rest)
     else if c = #"\"" then (* read string *)
       let (t,rest) = read_string str "" in
         SOME (t, rest)
     else if isPREFIX "*)" (c::str) then
       SOME (ErrorS, TL str)
     else if isPREFIX "#\"" (c::str) then
       let (t,rest) = read_string (TL str) "" in
         SOME (mkCharS t, rest)
     else if isPREFIX "(*" (c::str) then
       case skip_comment (TL str) 0 of
       | NONE => SOME (ErrorS, "")
       | SOME rest => next_sym_alt rest
     else if is_single_char_symbol c then (* single character tokens, i.e. delimiters *)
       SOME (OtherS [c], str)
     else if isSymbol c then
       let (n,rest) = read_while isSymbol str [c] in
         SOME (OtherS n, rest)
     else if isAlpha c then (* read identifier *)
       let (n,rest) = read_while isAlphaNumPrime str [c] in
         case rest of
              #"."::rest' =>
                  (case rest' of
                      c'::rest' =>
                        if isAlpha c' then
                          let (n', rest'') = read_while isAlphaNumPrime rest' [c'] in
                            SOME (LongS (n ++ "." ++ n'), rest'')
                        else if isSymbol c' then
                          let (n', rest'') = read_while isSymbol rest' [c'] in
                            SOME (LongS (n ++ "." ++ n'), rest'')
                             else
                               SOME (ErrorS, rest')
                    | "" => SOME (ErrorS, []))
            | _ => SOME (OtherS n, rest)
     else if c = #"_" then SOME (OtherS "_", str)
     else (* input not recognised *)
       SOME (ErrorS, str))`
 (WF_REL_TAC `measure LENGTH` THEN REPEAT STRIP_TAC
   THEN IMP_RES_TAC (GSYM read_while_thm)
   THEN IMP_RES_TAC (GSYM read_string_thm)
   THEN IMP_RES_TAC skip_comment_thm THEN Cases_on `str`
   THEN FULL_SIMP_TAC (srw_ss()) [LENGTH] THEN DECIDE_TAC)

val EVERY_isDigit_imp = Q.prove(`
  EVERY isDigit x ⇒
  MAP UNHEX x = MAP unhex_alt x`,
  rw[]>>match_mp_tac LIST_EQ>>fs[EL_MAP,EVERY_EL,unhex_alt_def,isDigit_def,isHexDigit_def])

val toNum_rw = Q.prove(`
  ∀x. EVERY isDigit x ⇒
  toNum x = num_from_dec_string_alt x`,
  rw[ASCIInumbersTheory.s2n_def,ASCIInumbersTheory.num_from_dec_string_def,num_from_dec_string_alt_def]>>
  AP_TERM_TAC>>
  match_mp_tac EVERY_isDigit_imp>>
  metis_tac[rich_listTheory.EVERY_REVERSE])

val EVERY_isHexDigit_imp = Q.prove(`
  EVERY isHexDigit x ⇒
  MAP UNHEX x = MAP unhex_alt x`,
  rw[]>>match_mp_tac LIST_EQ>>fs[EL_MAP,EVERY_EL,unhex_alt_def])

val num_from_hex_string_rw = Q.prove(`
  ∀x. EVERY isHexDigit x ⇒
  num_from_hex_string x = num_from_hex_string_alt x`,
  rw[ASCIInumbersTheory.s2n_def,ASCIInumbersTheory.num_from_hex_string_def,num_from_hex_string_alt_def]>>
  AP_TERM_TAC>>
  match_mp_tac EVERY_isHexDigit_imp>>
  metis_tac[rich_listTheory.EVERY_REVERSE])

val EVERY_IMPLODE = Q.prove(`
  ∀ls P.
  EVERY P (IMPLODE ls) ⇔ EVERY P ls`,
  Induct>>fs[])

val read_while_P_lem = Q.prove(`
  ∀ls rest P x y.
  EVERY P rest ∧
  read_while P ls rest = (x,y) ⇒
  EVERY P x`,
  Induct>>fs[read_while_def]>>rw[]>>
  fs[EVERY_IMPLODE,rich_listTheory.EVERY_REVERSE]>>
  first_assum match_mp_tac>>fs[]>>
  qexists_tac`STRING h rest`>>fs[])

val read_while_P = Q.prove(`
  ∀ls P x y.
  read_while P ls "" = (x,y) ⇒
  EVERY P x`,
  rw[]>>ho_match_mp_tac read_while_P_lem>>
  MAP_EVERY qexists_tac [`ls`,`""`,`y`]>>fs[])

val next_sym_eq = Q.store_thm("next_sym_eq",
  `∀x. next_sym x = next_sym_alt x`,
  ho_match_mp_tac next_sym_ind>>fs[next_sym_def,next_sym_alt_def]>>rw[]>>
  TRY(BasicProvers.TOP_CASE_TAC>>fs[]>>NO_TAC)>>
  TRY(rpt(pop_assum mp_tac)>> EVAL_TAC>> simp[]>>NO_TAC)>>
  pairarg_tac>>fs[]>>
  TRY(qmatch_goalsub_abbrev_tac`num_from_hex_string _ = _` >> match_mp_tac num_from_hex_string_rw)>>
  TRY(qmatch_goalsub_abbrev_tac`toNum _ = _` >>match_mp_tac toNum_rw)>>
  fs[]>>
  ho_match_mp_tac read_while_P>>
  metis_tac[]);

(* lex_until_toplevel_semicolon *)

val lex_aux_def = tDefine "lex_aux" `
  lex_aux acc (d:num) input =
    case next_token input of
    | (* case: end of input *)
      NONE => NONE
    | (* case: token found *)
      SOME (token, rest) =>
        let new_acc = (token::acc) in
          if token = SemicolonT /\ (d = 0) then SOME (REVERSE new_acc, rest)
          else
            if token = LetT then lex_aux new_acc (d + 1) rest
            else if token = StructT then lex_aux new_acc (d + 1) rest
            else if token = SigT then lex_aux new_acc (d + 1) rest
            else if token = LparT then lex_aux new_acc (d + 1) rest
            else if token = EndT then lex_aux new_acc (d - 1) rest
            else if token = RparT then lex_aux new_acc (d - 1) rest
            else lex_aux new_acc d rest `
  (WF_REL_TAC `measure (LENGTH o SND o SND)`
   THEN SRW_TAC []  [next_token_LESS]);

val lex_until_toplevel_semicolon_def = Define `
  lex_until_toplevel_semicolon input = lex_aux [] 0 input`;

val lex_aux_LESS = Q.prove(
  `!acc d input.
      (lex_aux acc d input = SOME (ts, rest)) ==>
      if acc = [] then LENGTH rest < LENGTH input
                  else LENGTH rest <= LENGTH input`,
  HO_MATCH_MP_TAC (fetch "-" "lex_aux_ind")
  THEN REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC
  THEN ONCE_REWRITE_TAC [lex_aux_def]
  THEN Cases_on `next_token input` THEN FULL_SIMP_TAC (srw_ss()) []
  THEN Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  THEN SRW_TAC [] [] THEN IMP_RES_TAC next_token_LESS
  THEN FULL_SIMP_TAC std_ss [] THEN RES_TAC
  THEN IMP_RES_TAC arithmeticTheory.LESS_TRANS
  THEN TRY (Cases_on `h`) THEN FULL_SIMP_TAC (srw_ss()) []
  THEN RES_TAC THEN IMP_RES_TAC arithmeticTheory.LESS_EQ_LESS_TRANS
  THEN IMP_RES_TAC (DECIDE ``n < m ==> n <= m:num``)
  THEN DECIDE_TAC);

val lex_until_toplevel_semicolon_LESS = Q.store_thm(
  "lex_until_toplevel_semicolon_LESS",
  `(lex_until_toplevel_semicolon input = SOME (ts,rest)) ==>
    LENGTH rest < LENGTH input`,
  SIMP_TAC std_ss [lex_until_toplevel_semicolon_def]
  THEN REPEAT STRIP_TAC THEN IMP_RES_TAC lex_aux_LESS
  THEN FULL_SIMP_TAC std_ss []);

(* lex_until_toplevel_semicolon_alt *)

open rich_listTheory

val lex_aux_alt_def = tDefine "lex_aux_alt" `
  lex_aux_alt acc (d:num) input =
    case next_sym input of
    | (* case: end of input *)
      NONE => NONE
    | (* case: token found *)
      SOME (token, rest) =>
        let new_acc = (token::acc) in
          if (token = OtherS ";") /\ (d = 0) then SOME (REVERSE new_acc, rest)
          else if MEM token [OtherS "let"; OtherS "struct";
                             OtherS "sig"; OtherS "("] then
            lex_aux_alt new_acc (d + 1) rest
          else if MEM token [OtherS ")"; OtherS "end"] then
            lex_aux_alt new_acc (d - 1) rest
          else lex_aux_alt new_acc d rest `
  (WF_REL_TAC `measure (LENGTH o SND o SND)`
   THEN SRW_TAC []  [next_sym_LESS]);

val lex_until_top_semicolon_alt_def = Define `
  lex_until_top_semicolon_alt input = lex_aux_alt [] 0 input`

val lex_aux_alt_LESS = Q.prove(
  `!acc d input.
      (lex_aux_alt acc d input = SOME (ts, rest)) ==>
      if acc = [] then LENGTH rest < LENGTH input
                  else LENGTH rest <= LENGTH input`,
  HO_MATCH_MP_TAC (fetch "-" "lex_aux_alt_ind")
  THEN REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC
  THEN ONCE_REWRITE_TAC [lex_aux_alt_def]
  THEN Cases_on `next_sym input` THEN FULL_SIMP_TAC (srw_ss()) []
  THEN Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  THEN SRW_TAC [] [] THEN IMP_RES_TAC next_sym_LESS
  THEN FULL_SIMP_TAC std_ss [] THEN RES_TAC
  THEN IMP_RES_TAC arithmeticTheory.LESS_TRANS
  THEN TRY (Cases_on `h`) THEN FULL_SIMP_TAC (srw_ss()) []
  THEN RES_TAC THEN IMP_RES_TAC arithmeticTheory.LESS_EQ_LESS_TRANS
  THEN IMP_RES_TAC (DECIDE ``n < m ==> n <= m:num``)
  THEN DECIDE_TAC);

val lex_until_top_semicolon_alt_LESS = Q.store_thm(
  "lex_until_top_semicolon_alt_LESS",
  `(lex_until_top_semicolon_alt input = SOME (ts,rest)) ==>
    LENGTH rest < LENGTH input`,
  SIMP_TAC std_ss [lex_until_top_semicolon_alt_def]
  THEN REPEAT STRIP_TAC THEN IMP_RES_TAC lex_aux_alt_LESS
  THEN FULL_SIMP_TAC std_ss []);

val token_of_sym_EQ_LEMMA = Q.prove(
  `((token_of_sym q = LetT) = (q = OtherS "let")) /\
    ((token_of_sym q = EndT) = (q = OtherS "end")) /\
    ((token_of_sym q = SigT) = (q = OtherS "sig")) /\
    ((token_of_sym q = StructT) = (q = OtherS "struct")) /\
    ((token_of_sym q = SemicolonT) = (q = OtherS ";")) /\
    ((token_of_sym q = RparT) = (q = OtherS ")")) /\
    ((token_of_sym q = LparT) = (q = OtherS "("))`,
  REPEAT STRIP_TAC
  THEN SIMP_TAC std_ss [token_of_sym_def,get_token_def,processIdent_def,LET_DEF]
  THEN BasicProvers.FULL_CASE_TAC THEN SRW_TAC [] []
  THEN CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) THEN SRW_TAC [] []
  THEN BasicProvers.FULL_CASE_TAC THEN SRW_TAC [] []
  THEN CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) THEN SRW_TAC [] []);

val lex_aux_alt_thm = Q.prove(
  `!acc d input.
      case lex_aux_alt acc d input of
      | NONE => (lex_aux (MAP token_of_sym acc) d input = NONE)
      | SOME (ts,rest) => (lex_aux (MAP token_of_sym acc) d input =
                           SOME (MAP token_of_sym ts,rest))`,
  HO_MATCH_MP_TAC (fetch "-" "lex_aux_alt_ind") THEN REPEAT STRIP_TAC
  THEN ONCE_REWRITE_TAC [lex_aux_alt_def,lex_aux_def]
  THEN SIMP_TAC std_ss [next_token_def]
  THEN Cases_on `next_sym input` THEN1 EVAL_TAC
  THEN Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  THEN FULL_SIMP_TAC std_ss [token_of_sym_EQ_LEMMA]
  THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [rich_listTheory.MAP_REVERSE]
  THEN FULL_SIMP_TAC (srw_ss()) [token_of_sym_def,get_token_def])
  |> Q.SPECL [`[]`,`0`] |> SIMP_RULE std_ss [MAP];

val lex_until_top_semicolon_alt_thm = Q.store_thm(
  "lex_until_top_semicolon_alt_thm",
  `case lex_until_top_semicolon_alt input of
    | NONE => (lex_until_toplevel_semicolon input = NONE)
    | SOME (ts,rest) =>
        (lex_until_toplevel_semicolon input = SOME (MAP token_of_sym ts,rest))`,
  SIMP_TAC std_ss [lex_until_top_semicolon_alt_def,
    lex_until_toplevel_semicolon_def,lex_aux_alt_thm]);

(* lex_impl_all *)

val lex_impl_all_def = tDefine "lex_impl_all" `
  lex_impl_all input =
    case lex_until_toplevel_semicolon input of
      | NONE => []
      | SOME (t,input') => t::lex_impl_all input'`
  (WF_REL_TAC `measure LENGTH` >>
   rw [] >>
   metis_tac [lex_until_toplevel_semicolon_LESS]);

val lex_aux_tokens_def = Define `
  lex_aux_tokens acc (d:num) input =
     case input of
       [] => NONE
     | token::rest =>
         let new_acc = token::acc in
           if token = SemicolonT /\ (d = 0) then
             SOME (REVERSE (new_acc),rest)
           else
             if token = LetT then
               lex_aux_tokens new_acc (d+1) rest
             else if token = StructT then
               lex_aux_tokens new_acc (d+1) rest
             else if token = SigT then
               lex_aux_tokens new_acc (d+1) rest
             else if token = LparT then
               lex_aux_tokens new_acc (d+1) rest
             else if token = EndT then
               lex_aux_tokens new_acc (d-1) rest
             else if token = RparT then
               lex_aux_tokens new_acc (d-1) rest
             else lex_aux_tokens new_acc d rest`

val lex_until_toplevel_semicolon_tokens_def = Define `
  lex_until_toplevel_semicolon_tokens input = lex_aux_tokens [] 0 input`;

val lex_aux_tokens_LESS = Q.prove(
  `!acc d input.
      (lex_aux_tokens acc d input = SOME (t,rest)) ==>
      (if acc = [] then LENGTH rest < LENGTH input
                   else LENGTH rest <= LENGTH input)`,
  Induct_on `input`
  THEN1 (EVAL_TAC >> SRW_TAC [] [LENGTH] >> SRW_TAC [] [LENGTH])
  >> SIMP_TAC (srw_ss()) [Once lex_aux_tokens_def,LET_DEF]
  >> SRW_TAC [] [] >> RES_TAC
  >> FULL_SIMP_TAC std_ss [NOT_CONS_NIL]
  >> TRY (Cases_on `h`) >> RES_TAC
  >> FULL_SIMP_TAC (srw_ss()) [] >> RES_TAC
  >> FULL_SIMP_TAC (srw_ss()) [] >> RES_TAC
  >> DECIDE_TAC);

val lex_impl_all_tokens_def = tDefine "lex_impl_all_tokens" `
  lex_impl_all_tokens input =
     case lex_until_toplevel_semicolon_tokens input of
       NONE => []
     | SOME (t,input) => t::lex_impl_all_tokens input`
  (WF_REL_TAC `measure LENGTH`
   >> SIMP_TAC std_ss [lex_until_toplevel_semicolon_tokens_def]
   >> METIS_TAC [lex_aux_tokens_LESS])

val lex_aux_tokens_thm = Q.prove(
  `!input acc d res1 res2.
      (lex_aux_tokens acc d (lexer_fun input) = res1) /\
      (lex_aux acc d input = res2) ==>
      (case res2 of NONE => (res1 = NONE)
                  | SOME (ts,rest) => (res1 = SOME (ts,lexer_fun rest)))`,
  HO_MATCH_MP_TAC lexer_fun_ind >> SIMP_TAC std_ss []
  >> REPEAT STRIP_TAC >> SIMP_TAC std_ss [Once lex_aux_def]
  >> ONCE_REWRITE_TAC [lexer_fun_def]
  >> ONCE_REWRITE_TAC [lex_aux_tokens_def]
  >> Cases_on `next_token input` >> ASM_SIMP_TAC (srw_ss()) []
  >> Cases_on `x`
  >> Q.MATCH_ASSUM_RENAME_TAC `next_token input = SOME (t,rest)`
  >> FULL_SIMP_TAC (srw_ss()) []
  >> SRW_TAC [] [] >> SRW_TAC [] []
  >> ASM_SIMP_TAC std_ss [GSYM lexer_fun_def]) |> SIMP_RULE std_ss [];

val lex_impl_all_tokens_thm = Q.prove(
  `!input. lex_impl_all input =
            lex_impl_all_tokens (lexer_fun input)`,
  HO_MATCH_MP_TAC (fetch "-" "lex_impl_all_ind") >> REPEAT STRIP_TAC
  >> SIMP_TAC std_ss [Once lex_impl_all_def,Once lex_impl_all_tokens_def]
  >> FULL_SIMP_TAC std_ss [lex_until_toplevel_semicolon_tokens_def]
  >> FULL_SIMP_TAC std_ss [lex_until_toplevel_semicolon_def]
  >> MP_TAC (lex_aux_tokens_thm |> Q.SPECL [`input`,`[]`,`0`])
  >> Cases_on `lex_aux [] 0 input` >> FULL_SIMP_TAC std_ss []
  >> Cases_on `x` >> FULL_SIMP_TAC (srw_ss()) []
  >> REPEAT STRIP_TAC >> RES_TAC);

val lex_aux_tokens_thm = Q.prove(
  `!input d acc.
      (res = lex_aux_tokens acc d input) ==>
      case res of
        NONE => (toplevel_semi_dex (LENGTH acc) d input = NONE)
      | SOME (toks,rest) =>
          (toplevel_semi_dex (LENGTH acc) d input = SOME (LENGTH toks)) /\
          (REVERSE acc ++ input = toks ++ rest)`,
  Induct
  >> SIMP_TAC (srw_ss()) [Once lex_aux_tokens_def]
  >> ONCE_REWRITE_TAC [toplevel_semi_dex_def]
  >> SIMP_TAC std_ss [LET_DEF] >> Cases
  >> FULL_SIMP_TAC (srw_ss()) []
  >> REPEAT STRIP_TAC >> RES_TAC
  >> POP_ASSUM MP_TAC
  >> POP_ASSUM (ASSUME_TAC o GSYM)
  >> ASM_REWRITE_TAC []
  >> Cases_on `res` >> SIMP_TAC (srw_ss()) [arithmeticTheory.ADD1]
  >> Cases_on `d = 0` >> ASM_SIMP_TAC (srw_ss()) [arithmeticTheory.ADD1]
  >> TRY (Cases_on `x`) >> SIMP_TAC (srw_ss()) [arithmeticTheory.ADD1]
  >> SIMP_TAC std_ss [Once EQ_SYM_EQ]
  >> FULL_SIMP_TAC std_ss []
  >> REPEAT STRIP_TAC >> RES_TAC
  >> FULL_SIMP_TAC (srw_ss()) [LENGTH,arithmeticTheory.ADD1])
  |> Q.SPECL [`input`,`0`,`[]`] |> Q.GEN `res` |> SIMP_RULE std_ss [LENGTH];

val split_top_level_semi_thm = Q.prove(
  `!input. split_top_level_semi input = lex_impl_all_tokens input`,
  HO_MATCH_MP_TAC split_top_level_semi_ind >> REPEAT STRIP_TAC
  >> SIMP_TAC std_ss [Once split_top_level_semi_def,Once lex_impl_all_tokens_def,
      Once lex_until_toplevel_semicolon_tokens_def]
  >> MP_TAC lex_aux_tokens_thm
  >> Cases_on `lex_aux_tokens [] 0 input` >> FULL_SIMP_TAC std_ss []
  >> Cases_on `x` >> FULL_SIMP_TAC (srw_ss()) []
  >> FULL_SIMP_TAC std_ss [TAKE_LENGTH_APPEND,DROP_LENGTH_APPEND]
  >> STRIP_TAC >> RES_TAC >> POP_ASSUM MP_TAC
  >> FULL_SIMP_TAC std_ss [TAKE_LENGTH_APPEND,DROP_LENGTH_APPEND]);

val lexer_correct = Q.store_thm("lexer_correct",
  `!input. split_top_level_semi (lexer_fun input) = lex_impl_all input`,
  SIMP_TAC std_ss [lex_impl_all_tokens_thm,split_top_level_semi_thm]);

val _ = export_theory();
