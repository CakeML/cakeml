(*
  Definition of the lexer: code for consuming tokens until a top-level
  semicolon is found (semicolons can be hidden in `let`-`in`-`end` blocks,
  structures, signatures, and between parentheses).
*)

open preamble tokensTheory lexer_funTheory

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory "lexer_impl";
val _ = set_grammar_ancestry ["misc", "tokens", "lexer_fun", "ASCIInumbers", "location"]

val tac =
 full_simp_tac (srw_ss()) [char_le_def, char_lt_def] >>
 Cases_on `t` >>
 rw [get_token_def, processIdent_def, isAlphaNum_def, isAlpha_def, isDigit_def,
     isLower_def, isUpper_def];

Theorem get_token_eqn:
 !s.
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
             SymbolT s
Proof
 strip_tac >>
 Cases_on `s` >>
 simp_tac (srw_ss()) []
 >- srw_tac [] [processIdent_def, get_token_def] >>
 MAP_EVERY (fn c =>
               Cases_on `h = ^c` >-
               tac >>
               full_simp_tac (srw_ss()) [])
           [``#"a"``, ``#"c"``, ``#"d"``, ``#"e"``, ``#"f"``, ``#"h"``,
            “#"i"”, ``#"l"``, ``#"o"``, ``#"r"``, ``#"s"``, ``#"t"``, ``#"w"``,
            “#"v"”, ``#"'"``, ``#"."``, ``#":"``, ``#"-"``, ``#"="``, ``#"#"``,
            “#"("”, ``#")"``, ``#"*"``, ``#","``, ``#";"``, ``#"|"``, ``#"["``,
            “#"]"”, ``#"_"``, ``#"{"``, ``#"}"``] >>
 full_simp_tac (srw_ss()) [get_token_def] >>
 rw [processIdent_def, isAlphaNum_def, isAlpha_def, isDigit_def,
     isLower_def, isUpper_def] >>
 full_simp_tac (srw_ss()++ARITH_ss) [char_le_def, char_lt_def] >>
 Cases_on `t` >>
 rw []
QED

val _ = computeLib.add_persistent_funs(["get_token_eqn"]);

Definition unhex_alt_def:
  unhex_alt x = (if isHexDigit x then UNHEX x else 0n)
End

Definition num_from_dec_string_alt_def:
  num_from_dec_string_alt = s2n 10 unhex_alt
End
Definition num_from_hex_string_alt_def:
  num_from_hex_string_alt = s2n 16 unhex_alt
End

Definition next_sym_alt_def:
  (next_sym_alt "" _ = NONE) /\
  (next_sym_alt (c::str) loc =
     if c = #"\n" then (* skip new line *)
        next_sym_alt str (next_line loc)
     else if isSpace c then (* skip blank space *)
       next_sym_alt str (next_loc 1 loc)
     else if isDigit c then (* read number *)
       if str ≠ "" ∧ c = #"0" ∧ HD str = #"w" then
         if TL str = "" then SOME (ErrorS, Locs loc loc, "")
         else if isDigit (HD (TL str)) then
           let (n,rest) = read_while isDigit (TL str) [] in
             SOME (WordS (num_from_dec_string_alt n),
                   Locs loc (next_loc (LENGTH n + 1) loc),
                   rest)
         else if HD(TL str) = #"x" then
           let (n,rest) = read_while isHexDigit (TL (TL str)) [] in
             SOME (WordS (num_from_hex_string_alt n),
                   Locs loc (next_loc (LENGTH n + 2) loc),
                   rest)
         else SOME (ErrorS, Locs loc loc, TL str)
       else
         if str ≠ "" ∧ c = #"0" ∧ HD str = #"x" then
           let (n,rest) = read_while isHexDigit (TL str) [] in
             SOME (NumberS (& num_from_hex_string_alt n),
                   Locs loc (next_loc (LENGTH n) loc),
                   rest)
         else
           let (n,rest) = read_while isDigit str [] in
             SOME (NumberS (&(num_from_dec_string_alt (c::n))),
                   Locs loc (next_loc (LENGTH n) loc),
                   rest)
     else if c = #"~" /\ str <> "" /\ isDigit (HD str) then (* read negative number *)
       let (n,rest) = read_while isDigit str [] in
         SOME (NumberS (0- &(num_from_dec_string_alt n)),
               Locs loc (next_loc (LENGTH n + 1) loc),
               rest)
     else if c = #"'" then (* read type variable *)
       let (n,rest) = read_while isAlphaNumPrime str [c] in
         SOME (OtherS n,
               Locs loc (next_loc (LENGTH n - 1) loc),
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
       let (t, loc', rest) =
             read_FFIcall (TL str) "" (next_loc 2 loc)
       in
         SOME (t, Locs loc loc', rest)
     else if isPREFIX "(*" (c::str) then
       case skip_comment (TL str) (0:num) (next_loc 2 loc) of
       | NONE => SOME (ErrorS, Locs loc (next_loc 2 loc), "")
       | SOME (rest, loc') => next_sym_alt rest loc'
     else if c = #"_" then SOME (OtherS "_", Locs loc loc, str) else
       let (tok,end_loc,rest) = read_Ident (STRING c str) loc [] in
         SOME (tok,Locs loc end_loc,rest))
Termination
   WF_REL_TAC `measure (LENGTH o FST) ` THEN REPEAT STRIP_TAC
   THEN IMP_RES_TAC (GSYM read_while_thm)
   THEN IMP_RES_TAC (GSYM read_string_thm)
   THEN IMP_RES_TAC skip_comment_thm THEN Cases_on `str`
   THEN FULL_SIMP_TAC (srw_ss()) [LENGTH] THEN DECIDE_TAC
End

Triviality EVERY_isDigit_imp:
  EVERY isDigit x ⇒
  MAP UNHEX x = MAP unhex_alt x
Proof
  rw[]>>match_mp_tac LIST_EQ>>fs[EL_MAP,EVERY_EL,unhex_alt_def,isDigit_def,isHexDigit_def]
QED

Triviality toNum_rw:
  ∀x. EVERY isDigit x ⇒
  toNum x = num_from_dec_string_alt x
Proof
  rw[ASCIInumbersTheory.s2n_def,ASCIInumbersTheory.num_from_dec_string_def,num_from_dec_string_alt_def]>>
  AP_TERM_TAC>>
  match_mp_tac EVERY_isDigit_imp>>
  metis_tac[rich_listTheory.EVERY_REVERSE]
QED

Triviality EVERY_isHexDigit_imp:
  EVERY isHexDigit x ⇒
  MAP UNHEX x = MAP unhex_alt x
Proof
  rw[]>>match_mp_tac LIST_EQ>>fs[EL_MAP,EVERY_EL,unhex_alt_def]
QED

Triviality num_from_hex_string_rw:
  ∀x. EVERY isHexDigit x ⇒
      num_from_hex_string x = num_from_hex_string_alt x
Proof
  rw[ASCIInumbersTheory.s2n_def,ASCIInumbersTheory.num_from_hex_string_def,num_from_hex_string_alt_def]>>
  AP_TERM_TAC>>
  match_mp_tac EVERY_isHexDigit_imp>>
  metis_tac[rich_listTheory.EVERY_REVERSE]
QED

Triviality EVERY_IMPLODE:
  ∀ls P.
    EVERY P (IMPLODE ls) ⇔ EVERY P ls
Proof
  Induct>>fs[]
QED

Triviality read_while_P_lem:
  ∀ls rest P x y.
    EVERY P rest ∧
    read_while P ls rest = (x,y) ⇒
    EVERY P x
Proof
  Induct>>fs[read_while_def]>>rw[]>>
  fs[EVERY_IMPLODE,rich_listTheory.EVERY_REVERSE]>>
  first_assum match_mp_tac>>fs[]>>
  qexists_tac`STRING h rest`>>fs[]
QED

Theorem read_while_P[local]:
  ∀ls P x y. read_while P ls "" = (x,y) ⇒ EVERY P x
Proof
  rw[]>>ho_match_mp_tac read_while_P_lem>>
  MAP_EVERY qexists_tac [`ls`,`""`,`y`]>>fs[]
QED

Theorem next_sym_eq:
  ∀x l. next_sym x l = next_sym_alt x l
Proof
  ho_match_mp_tac next_sym_ind
  \\ fs[next_sym_def,next_sym_alt_def] \\ rw [] >>
  TRY(BasicProvers.TOP_CASE_TAC>>fs[]>>NO_TAC)>>
  TRY(rpt(pop_assum mp_tac)>> EVAL_TAC>> simp[]>>NO_TAC)>>
  TRY(pairarg_tac) >>fs[]>>
  TRY(qmatch_goalsub_abbrev_tac`num_from_hex_string _ = _` >>
      match_mp_tac num_from_hex_string_rw)>>
  TRY(qmatch_goalsub_abbrev_tac`toNum _ = _` >>match_mp_tac toNum_rw)>>
  TRY(fs[]>>
      ho_match_mp_tac read_while_P>>
      metis_tac[]) >>
  every_case_tac >> metis_tac[]
QED

(* lex_until_toplevel_semicolon *)

Definition lex_aux_def:
  lex_aux acc (d:num) input loc =
    case next_token input loc of
    | (* case: end of input *)
      NONE => NONE
    | (* case: token found *)
      SOME (token, Locs loc' loc'', rest) =>
        let new_acc = ((token, Locs loc' loc'')::acc) in
        let newloc = next_loc 1 loc'' in
          if token = SemicolonT /\ (d = 0) then SOME (REVERSE new_acc, newloc, rest)
          else
            if token = LetT then lex_aux new_acc (d + 1) rest newloc
            else if token = StructT then lex_aux new_acc (d + 1) rest newloc
            else if token = SigT then lex_aux new_acc (d + 1) rest newloc
            else if token = LparT then lex_aux new_acc (d + 1) rest newloc
            else if token = EndT then lex_aux new_acc (d - 1) rest newloc
            else if token = RparT then lex_aux new_acc (d - 1) rest newloc
            else lex_aux new_acc d rest newloc
Termination
  WF_REL_TAC `measure (LENGTH o FST o SND o SND)` >> rw[] >>
  imp_res_tac next_token_LESS
End

Definition lex_until_toplevel_semicolon_def:
  lex_until_toplevel_semicolon input = lex_aux [] 0 input
End

Triviality lex_aux_LESS:
  !acc d input l.
      (lex_aux acc d input l = SOME (ts, l', rest)) ==>
      if acc = [] then LENGTH rest < LENGTH input
                  else LENGTH rest <= LENGTH input
Proof
  HO_MATCH_MP_TAC (fetch "-" "lex_aux_ind")
  THEN REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC
  THEN ONCE_REWRITE_TAC [lex_aux_def]
  THEN Cases_on `next_token input l` THEN FULL_SIMP_TAC (srw_ss()) []
  THEN every_case_tac
  THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  THEN SRW_TAC [] [] THEN IMP_RES_TAC next_token_LESS
  THEN FULL_SIMP_TAC std_ss [] THEN RES_TAC
  THEN IMP_RES_TAC arithmeticTheory.LESS_TRANS
  THEN TRY (Cases_on `h`)
  THEN FULL_SIMP_TAC (srw_ss()) []
  THEN RES_TAC THEN IMP_RES_TAC arithmeticTheory.LESS_EQ_LESS_TRANS
  THEN IMP_RES_TAC (DECIDE ``n < m ==> n <= m:num``)
  THEN DECIDE_TAC
QED

Theorem lex_until_toplevel_semicolon_LESS:
   (lex_until_toplevel_semicolon input l = SOME (ts, l', rest)) ==>
    LENGTH rest < LENGTH input
Proof
  SIMP_TAC std_ss [lex_until_toplevel_semicolon_def]
  THEN REPEAT STRIP_TAC THEN IMP_RES_TAC lex_aux_LESS
  THEN FULL_SIMP_TAC std_ss []
QED

(* lex_until_toplevel_semicolon_alt *)

open rich_listTheory

Definition lex_aux_alt_def:
  lex_aux_alt acc (d:num) input l =
    case next_sym input l of
    | (* case: end of input *)
      NONE => NONE
    | (* case: token found *)
      SOME (token, Locs loc' loc'', rest) =>
        let new_acc = ((token, Locs loc' loc'')::acc) in
        let newloc = next_loc 1 loc'' in
          if (token = OtherS ";") /\ (d = 0) then SOME (REVERSE new_acc, newloc, rest)
          else if MEM token [OtherS "let"; OtherS "struct";
                             OtherS "sig"; OtherS "("] then
            lex_aux_alt new_acc (d + 1) rest newloc
          else if MEM token [OtherS ")"; OtherS "end"] then
            lex_aux_alt new_acc (d - 1) rest newloc
          else lex_aux_alt new_acc d rest newloc
Termination
  WF_REL_TAC `measure (LENGTH o FST o SND o SND)` >> rw[] >>
  imp_res_tac next_sym_LESS
End

Definition lex_until_top_semicolon_alt_def:
  lex_until_top_semicolon_alt input = lex_aux_alt [] 0 input
End

Triviality lex_aux_alt_LESS:
  !acc d input l.
      (lex_aux_alt acc d input l = SOME (ts, l', rest)) ==>
      if acc = [] then LENGTH rest < LENGTH input
                  else LENGTH rest <= LENGTH input
Proof
  HO_MATCH_MP_TAC (fetch "-" "lex_aux_alt_ind")
  THEN REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC
  THEN ONCE_REWRITE_TAC [lex_aux_alt_def]
  THEN Cases_on `next_sym inputi l` THEN FULL_SIMP_TAC (srw_ss()) []
  THEN every_case_tac
  THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  THEN SRW_TAC [] [] THEN IMP_RES_TAC next_sym_LESS
  THEN FULL_SIMP_TAC std_ss [] THEN RES_TAC
  THEN IMP_RES_TAC arithmeticTheory.LESS_TRANS
  THEN TRY (Cases_on `h`) THEN FULL_SIMP_TAC (srw_ss()) []
  THEN RES_TAC THEN IMP_RES_TAC arithmeticTheory.LESS_EQ_LESS_TRANS
  THEN IMP_RES_TAC (DECIDE ``n < m ==> n <= m:num``)
  THEN DECIDE_TAC
QED

Theorem lex_until_top_semicolon_alt_LESS:
   (lex_until_top_semicolon_alt input l = SOME (ts, l', rest)) ==>
    LENGTH rest < LENGTH input
Proof
  SIMP_TAC std_ss [lex_until_top_semicolon_alt_def]
  THEN REPEAT STRIP_TAC THEN IMP_RES_TAC lex_aux_alt_LESS
  THEN FULL_SIMP_TAC std_ss []
QED

Theorem token_of_sym_EQ_LEMMA[local]:
  ((token_of_sym q = LetT) = (q = OtherS "let")) /\
  ((token_of_sym q = EndT) = (q = OtherS "end")) /\
  ((token_of_sym q = SigT) = (q = OtherS "sig")) /\
  ((token_of_sym q = StructT) = (q = OtherS "struct")) /\
  ((token_of_sym q = SemicolonT) = (q = OtherS ";")) /\
  ((token_of_sym q = RparT) = (q = OtherS ")")) /\
  ((token_of_sym q = LparT) = (q = OtherS "("))
Proof
  REPEAT STRIP_TAC THEN
  simp[token_of_sym_def,get_token_def,processIdent_def,LET_DEF,
       AllCaseEqs(), UNCURRY]
QED


Definition token_of_sym_loc_def:
  token_of_sym_loc (t, l) = (token_of_sym t, l)
End

val lex_aux_alt_thm = Q.prove(
  `!acc d input l.
      case lex_aux_alt acc d input l of
      | NONE => (lex_aux (MAP token_of_sym_loc acc) d input l = NONE)
      | SOME (ts, rest) => (lex_aux (MAP token_of_sym_loc acc) d input l =
                           SOME (MAP token_of_sym_loc ts,rest))`,
  HO_MATCH_MP_TAC (fetch "-" "lex_aux_alt_ind") THEN REPEAT STRIP_TAC
  THEN ONCE_REWRITE_TAC [lex_aux_alt_def,lex_aux_def]
  THEN SIMP_TAC std_ss [next_token_def]
  THEN Cases_on `next_sym input l` THEN1 EVAL_TAC
  THEN every_case_tac THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  THEN FULL_SIMP_TAC std_ss [token_of_sym_EQ_LEMMA]
  THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [rich_listTheory.MAP_REVERSE]
  THEN FULL_SIMP_TAC (srw_ss()) [token_of_sym_loc_def,token_of_sym_def,get_token_def])
  |> Q.SPECL [`[]`,`0`] |> SIMP_RULE std_ss [MAP] ;

Theorem lex_until_top_semicolon_alt_thm:
   case lex_until_top_semicolon_alt input l of
    | NONE => (lex_until_toplevel_semicolon input l = NONE)
    | SOME (ts,rest) =>
        (lex_until_toplevel_semicolon input l = SOME (MAP token_of_sym_loc ts,rest))
Proof
  SIMP_TAC std_ss [lex_until_top_semicolon_alt_def,
    lex_until_toplevel_semicolon_def,lex_aux_alt_thm]
QED

(* lex_impl_all *)

Definition lex_impl_all_def:
  lex_impl_all input l =
    case lex_until_toplevel_semicolon input l of
      | NONE => []
      | SOME (t, loc, input') => t ::lex_impl_all input' loc
Termination
  WF_REL_TAC `measure (LENGTH o FST)` >>
   rw [] >>
   metis_tac [lex_until_toplevel_semicolon_LESS]
End

Definition lex_aux_tokens_def:
  lex_aux_tokens acc (d:num) input =
     case input of
       [] => NONE
     | (token, locs)::rest =>
         let new_acc = (token, locs)::acc in
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
             else lex_aux_tokens new_acc d rest
End

Definition lex_until_toplevel_semicolon_tokens_def:
  lex_until_toplevel_semicolon_tokens input = lex_aux_tokens [] 0 input
End

Triviality lex_aux_tokens_LESS:
  !acc d input.
      (lex_aux_tokens acc d input = SOME (t,rest)) ==>
      (if acc = [] then LENGTH rest < LENGTH input
                   else LENGTH rest <= LENGTH input)
Proof
  Induct_on `input`
  THEN1 (EVAL_TAC >> SRW_TAC [] [LENGTH] >> SRW_TAC [] [LENGTH])
  >> SIMP_TAC (srw_ss()) [Once lex_aux_tokens_def,LET_DEF]
  >> SRW_TAC [] [] >> RES_TAC
  >> FULL_SIMP_TAC std_ss [NOT_CONS_NIL]
  >> TRY (Cases_on `h`) >> RES_TAC
  >> FULL_SIMP_TAC (srw_ss()) [] >> RES_TAC
  >> FULL_SIMP_TAC (srw_ss()) [] >> RES_TAC
  >> Cases_on `q` >> Cases_on `d` >> fs[] >> res_tac >> fs[]
QED

Definition lex_impl_all_tokens_def:
  lex_impl_all_tokens input =
     case lex_until_toplevel_semicolon_tokens input of
       NONE => []
     | SOME (t,input) => t::lex_impl_all_tokens input
Termination
  WF_REL_TAC `measure LENGTH`
   >> SIMP_TAC std_ss [lex_until_toplevel_semicolon_tokens_def]
   >> METIS_TAC [lex_aux_tokens_LESS]
End

Triviality lex_aux_tokens_thm_1:
  !input l acc d res1 res2.
      (lex_aux_tokens acc d (lexer_fun_aux input l) = res1) /\
      (lex_aux acc d input l = res2) ==>
      (case res2 of NONE => (res1 = NONE)
          | SOME (ts, l', rest) =>
              (res1 = SOME (ts, lexer_fun_aux rest l')))
Proof
  HO_MATCH_MP_TAC lexer_fun_aux_ind >> SIMP_TAC std_ss []
  >> REPEAT STRIP_TAC >> SIMP_TAC std_ss [Once lex_aux_def]
  >> ONCE_REWRITE_TAC [lexer_fun_aux_def]
  >> ONCE_REWRITE_TAC [lex_aux_tokens_def]
  >> Cases_on `next_token input l ` >> ASM_SIMP_TAC (srw_ss()) []
  >> Cases_on `x`
  >> Q.MATCH_ASSUM_RENAME_TAC `next_token input l = SOME (t,rest)`
  >> Cases_on `rest`
  >> Cases_on `q`
  >> FULL_SIMP_TAC (srw_ss()) []
  >> SRW_TAC [] [] >> SRW_TAC [] []
  >> ASM_SIMP_TAC std_ss [GSYM lexer_fun_aux_def]
  >> gvs[]
QED

Triviality lex_aux_tokens_thm = lex_aux_tokens_thm_1 |> SIMP_RULE std_ss [];

Triviality lex_impl_all_tokens_thm:
  !input l. lex_impl_all input l =
            lex_impl_all_tokens (lexer_fun_aux input l)
Proof
  HO_MATCH_MP_TAC (fetch "-" "lex_impl_all_ind") >> REPEAT STRIP_TAC
  >> SIMP_TAC std_ss [Once lex_impl_all_def,Once lex_impl_all_tokens_def]
  >> fs [lex_until_toplevel_semicolon_tokens_def]
  >> fs [lex_until_toplevel_semicolon_def]
  >> MP_TAC (lex_aux_tokens_thm |> Q.SPECL [`input`, `l`, `[]`,`0`])
  >> Cases_on `lex_aux [] 0 input l` >> fs[]
  >> Cases_on `x` >> Cases_on `r` >> fs[]
QED

Triviality lex_aux_tokens_thm_1:
  !input d acc.
      case lex_aux_tokens acc d input of
        NONE => (toplevel_semi_dex (LENGTH acc) d input = NONE)
      | SOME (toks,rest) =>
          (toplevel_semi_dex (LENGTH acc) d input = SOME (LENGTH toks)) /\
          (REVERSE acc ++ input = toks ++ rest)
Proof
  Induct
  >> SIMP_TAC (srw_ss()) [Once lex_aux_tokens_def]
  >> ONCE_REWRITE_TAC [toplevel_semi_dex_def]
  >> SIMP_TAC std_ss [LET_DEF] >> Cases
  >> rw[]
  >> gvs [Once toplevel_semi_dex_def,LENGTH,arithmeticTheory.ADD1]
  >> qmatch_goalsub_abbrev_tac`lex_aux_tokens accc dd`
  >> first_x_assum (qspecl_then [`dd`,`accc`] assume_tac)
  >> gvs[AllCasePreds(),Abbr`accc`,ADD1,Abbr`dd`]
  >> gvs [Once toplevel_semi_dex_def,LENGTH,arithmeticTheory.ADD1]
  >> rw[]
QED

Triviality lex_aux_tokens_thm = lex_aux_tokens_thm_1
  |> Q.SPECL [`input`,`0`,`[]`] |> SIMP_RULE std_ss [LENGTH];

Triviality split_top_level_semi_thm:
  !input. split_top_level_semi input = lex_impl_all_tokens input
Proof
  HO_MATCH_MP_TAC split_top_level_semi_ind >> REPEAT STRIP_TAC
  >> SIMP_TAC std_ss [Once split_top_level_semi_def,Once lex_impl_all_tokens_def,
      Once lex_until_toplevel_semicolon_tokens_def]
  >> MP_TAC lex_aux_tokens_thm
  >> Cases_on `lex_aux_tokens [] 0 input` >> FULL_SIMP_TAC std_ss []
  >> Cases_on `x` >> FULL_SIMP_TAC (srw_ss()) []
  >> FULL_SIMP_TAC std_ss [TAKE_LENGTH_APPEND,DROP_LENGTH_APPEND]
  >> STRIP_TAC >> RES_TAC >> POP_ASSUM MP_TAC
  >> FULL_SIMP_TAC std_ss [TAKE_LENGTH_APPEND,DROP_LENGTH_APPEND]
QED

Theorem lexer_correct:
   !input. split_top_level_semi (lexer_fun_aux input l) = lex_impl_all input l
Proof
  SIMP_TAC std_ss [lex_impl_all_tokens_thm,split_top_level_semi_thm]
QED

val _ = export_theory();
