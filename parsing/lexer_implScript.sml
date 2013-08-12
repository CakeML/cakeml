
open HolKernel Parse boolLib bossLib lcsymtacs;

val _ = new_theory "lexer_impl";

open stringTheory stringLib listTheory TokensTheory lexer_funTheory;

val tac =
  BasicProvers.FULL_CASE_TAC
  >- (simp_tac (srw_ss()) [char_le_def, char_lt_def, get_token_def, processIdent_def] >>
      full_simp_tac (srw_ss()) [isAlphaNum_def, isAlpha_def, isDigit_def, 
                                isUpper_def, isLower_def]) >>
  pop_assum (fn _ => all_tac);

  (*
val get_token_eqn = Q.prove (
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
               if c ≤ #"=" then
                 if #"A" ≤ c ∧ c ≤ #"Z" then AlphaT s else
                 if c = #"=" then EqualsT else
                 SymbolT s
               else
                 if c = #"[" then LbrackT else
                 if c = #"]" then RbrackT else
                 SymbolT s
             else
               if c ≤ #"{" then
                 if #"a" ≤ c ∧ c ≤ #"z" then AlphaT s else
                 if c = #"{" then LbraceT else
                 SymbolT s
               else
                 if c = #"|" then BarT else
                 if c = #"}" then RbraceT else
                 SymbolT s
       | c::s' =>
           if c < #"a" then
             if c = #"'" then TyvarT s else
             if s = "->" then ArrowT else
             if s = "..." then DotsT else
             if s = ":>" then SealT else
             if s = "=>" then DarrowT else
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
 Cases_on `t` >>
 simp_tac (srw_ss()) [] >>
 NTAC 9 tac
 *)

val lex_aux_def = tDefine "lex_aux" `
  lex_aux acc error stk input =
    case next_token input of
    | (* case: end of input *)
      NONE => NONE
    | (* case: token found *)
      SOME (token, rest) =>
        if token = SemicolonT /\ (stk = [] \/ error) then SOME (REVERSE (token::acc), rest)
        else
          let new_acc = (token::acc) in
            if error then lex_aux new_acc error stk rest
            else if token = LetT then lex_aux new_acc F (SH_END::stk) rest
            else if token = StructT then lex_aux new_acc F (SH_END::stk) rest
            else if token = SigT then lex_aux new_acc F (SH_END::stk) rest
            else if token = LparT then lex_aux new_acc F (SH_PAR::stk) rest
            else if token = EndT then
              case stk of
                  SH_END :: stk' => lex_aux new_acc F stk' rest
                | _ => lex_aux new_acc T [] rest
            else if token = RparT then
              case stk of
                  SH_PAR :: stk' => lex_aux new_acc F stk' rest
                | _ => lex_aux new_acc T [] rest
            else lex_aux new_acc F stk rest `
  (WF_REL_TAC `measure (LENGTH o SND o SND o SND)`
   THEN SRW_TAC []  [next_token_LESS]);

val lex_until_toplevel_semicolon_def = Define `
  lex_until_toplevel_semicolon input = lex_aux [] F [] input`;

val lex_aux_LESS = prove(
  ``!acc error stk input.
      (lex_aux acc error stk input = SOME (ts, rest)) ==>
      if acc = [] then LENGTH rest < LENGTH input
                  else LENGTH rest <= LENGTH input``,
  HO_MATCH_MP_TAC (fetch "-" "lex_aux_ind")
  THEN REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC
  THEN ONCE_REWRITE_TAC [lex_aux_def]
  THEN Cases_on `next_token input` THEN FULL_SIMP_TAC (srw_ss()) []
  THEN Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  THEN SRW_TAC [] [] THEN IMP_RES_TAC next_token_LESS
  THEN FULL_SIMP_TAC std_ss [] THEN RES_TAC
  THEN IMP_RES_TAC arithmeticTheory.LESS_TRANS
  THEN TRY (Cases_on `stk`) THEN FULL_SIMP_TAC (srw_ss()) []
  THEN TRY (Cases_on `h`) THEN FULL_SIMP_TAC (srw_ss()) []
  THEN RES_TAC THEN IMP_RES_TAC arithmeticTheory.LESS_EQ_LESS_TRANS
  THEN IMP_RES_TAC (DECIDE ``n < m ==> n <= m:num``)
  THEN DECIDE_TAC);

val lex_until_toplevel_semicolon_LESS = store_thm(
  "lex_until_toplevel_semicolon_LESS",
  ``(lex_until_toplevel_semicolon input = SOME (ts,rest)) ==>
    LENGTH rest < LENGTH input``,
  SIMP_TAC std_ss [lex_until_toplevel_semicolon_def]
  THEN REPEAT STRIP_TAC THEN IMP_RES_TAC lex_aux_LESS
  THEN FULL_SIMP_TAC std_ss []);

val _ = export_theory();
