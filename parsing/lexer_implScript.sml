
open HolKernel Parse boolLib bossLib;

val _ = new_theory "lexer_impl";

open stringTheory stringLib listTheory TokensTheory lexer_funTheory;

val _ = Hol_datatype`semihider = SH_END | SH_PAR`
(* extend with SH_BRACE and SH_BRACKET when records and lists
   are part of the syntax *)

val lex_aux_def = tDefine "lex_aux" `
  lex_aux acc error stk input =
    case next_token input of
    | (* case: end of input *)
      NONE => if acc = [] then NONE else SOME (REVERSE acc,"")
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
      LENGTH rest < LENGTH input``,
  HO_MATCH_MP_TAC (fetch "-" "lex_aux_ind")
  THEN REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC
  THEN ONCE_REWRITE_TAC [lex_aux_def]
  THEN Cases_on `next_token input` THEN FULL_SIMP_TAC (srw_ss()) []
  THEN Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  THEN SRW_TAC [] [] THEN IMP_RES_TAC next_token_LESS
  THEN FULL_SIMP_TAC std_ss [] THEN RES_TAC
  THEN IMP_RES_TAC arithmeticTheory.LESS_TRANS
  THEN Cases_on `stk` THEN FULL_SIMP_TAC (srw_ss()) []
  THEN Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) []);

val lex_until_toplevel_semicolon_LESS = store_thm(
  "lex_until_toplevel_semicolon_LESS",
  ``(lex_until_toplevel_semicolon input = SOME (ts,rest)) ==>
    LENGTH rest < LENGTH input``,
  SIMP_TAC std_ss [lex_until_toplevel_semicolon_def]
  THEN REPEAT STRIP_TAC THEN IMP_RES_TAC lex_aux_LESS);

val _ = export_theory();
