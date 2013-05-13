open HolKernel Parse boolLib bossLib

open mmlPEGTheory mmlPtreeConversionTheory
open monadsyntax

val _ = new_theory "mmlParse"

val _ = overload_on ("mmlpegexec",
                     ``λn t. peg_exec mmlPEG (pnt n) t [] done failed``)

val destResult_def = Define`
  destResult (Result x) = x ∧
  destResult _ = NONE
`

val mmlParseExpr_def = Define`
  mmlParseExpr toks = do
    (toks', pts) <- destResult (mmlpegexec nE toks);
    ast <- ptree_Expr nE (HD pts);
    SOME(toks',ast)
  od
`;

val mmlParseREPLPhrase_def = Define`
  mmlParseREPLPhrase toks = do
    (toks', pts) <- destResult (mmlpegexec nREPLPhrase toks);
    ast <- ptree_REPLPhrase (HD pts);
    SOME(toks',ast)
  od
`

(* This function parses declarations, no junk is allowed at the end.
   It is used in implementation/repl_funScript.sml. *)
val parse_def = Define `
  (parse : token list -> ast_prog option) tokens =
    do
      (ts,ast_tdecs) <- mmlParseREPLPhrase tokens;
      if ts <> [] then NONE else SOME ast_tdecs
    od
`;

(* TODO: fix *)
val parse_top_def = Define `
  (parse_top : token list -> ast_top option) tokens =
    do
      (ts,ast_tdecs) <- mmlParseREPLPhrase tokens;
      if ts <> [] then NONE
      else case ast_tdecs of [top] => SOME top | _ => NONE
    od
`;


val _ = Hol_datatype`semihider = SH_END | SH_PAR`
(* extend with SH_BRACE and SH_BRACKET when records and lists
   are part of the syntax *)

val toplevel_semi_dex_def = Define`
  toplevel_semi_dex (i:num) error stk [] = NONE ∧
  toplevel_semi_dex i error stk (h::t) =
    if h = SemicolonT ∧ (stk = [] ∨ error) then SOME i
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

val splitAt_def = Define`
  splitAt _ [] k = k [] [] ∧
  splitAt n (h::t) k = if n = 0n then k [] (h::t)
                       else splitAt (n-1) t (λp. k (h :: p))
`
(*
assert
  (aconv ``([1n;2;3],[4n;5])`` o rhs o concl)
  (EVAL ``splitAt 3 [1n;2;3;4;5] (,)``);
assert
  (aconv ``([1n;2;3;4;5],[]:num list)`` o rhs o concl)
  (EVAL ``splitAt 7 [1n;2;3;4;5] (,)``)
*)

val _ = Hol_datatype`
  repl_parse_result = RPR_INCOMPLETE of token list
                    | RPR_PROG of ast_prog option => token list
`

val parse_REPLphrase_def = Define`
  parse_REPLphrase toks =
    do
      (toks',pts) <- destResult (mmlpegexec nREPLPhrase toks);
      tds <- ptree_REPLPhrase (HD pts);
      SOME(toks',tds)
    od
`

val repl_parse_step_def = Define`
  repl_parse_step toks =
    case toplevel_semi_dex 1 F [] toks of
      NONE => RPR_INCOMPLETE toks
    | SOME i => let (p,s) = splitAt i toks (,)
                in
                  case parse_REPLphrase p of
                      NONE => RPR_PROG NONE s
                    | SOME(p',tds) => RPR_PROG (SOME tds) (p' ++ s)
                                               (* p' should always be [] *)
`

(*
open lexer_funTheory;

Define`rstr s = repl_parse_step (lexer_fun s)`;

EVAL ``rstr "val x = 3 val y = 10; x + y;"``;

EVAL ``rstr "val x = 10 + val y = 10; x + y;"``;

EVAL ``rstr "val x = (10 + val y = 10; x + y;"``;
  (* Poly/ML and Moscow ML both detect the error in the above without
     calling for more input.  I don't know how they're doing this, but
     am not too bothered by not managing to replicate it. *)

EVAL ``rstr "val x = let val x = ) ; x + y;"``;
  (* the semi-colon finder and splitter do manage this one *)

EVAL ``rstr "; val x = 3; val y = 10; x + y;"``;

EVAL ``rstr "structure s :> sig val x : int end = struct \
            \val x = 10 + 101; end;"``

EVAL ``rstr "structure s :> sig datatype 'a list = Nil | Cons of 'a * 'a list; \
            \ val map : ('a -> 'b) -> 'a list -> 'b list; end = \
            \struct val x = 10; end; map f (Cons(x,y))"``;

*)


val _ = export_theory()
