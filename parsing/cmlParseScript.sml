open HolKernel Parse boolLib bossLib

open cmlPEGTheory cmlPtreeConversionTheory pegSoundTheory
open lcsymtacs
open monadsyntax

val _ = new_theory "cmlParse"

val _ = overload_on ("cmlpegexec",
                     ``λn t. peg_exec cmlPEG (pnt n) t [] done failed``)

val destResult_def = Define`
  destResult (Result x) = x ∧
  destResult _ = NONE
`

val cmlParseExpr_def = Define`
  cmlParseExpr toks = do
    (toks', pts) <- destResult (cmlpegexec nE toks);
    pt <- oHD pts;
    ast <- ptree_Expr nE pt;
    SOME(toks',ast)
  od
`;

val cmlParseREPLTop_def = Define`
  cmlParseREPLTop toks = do
    (toks', pts) <- destResult (cmlpegexec nREPLTop toks);
    pt <- oHD pts;
    ast <- ptree_REPLTop pt;
    SOME(toks',ast)
  od
`

val cmlpeg_executed =
    pegexecTheory.peg_eval_executed
      |> Q.GEN `G` |> Q.ISPEC `cmlPEG`
      |> SIMP_RULE (srw_ss()) [cmlPEGTheory.PEG_wellformed]
      |> Q.GEN `s` |> Q.GEN `r` |> Q.GEN `e` |> GSYM

(* This function parses a single declaration followed by a semicolon.
   No junk is allowed at the end.
   It is used in repl/repl_funScript.sml. *)
val parse_top_def = Define `
  (parse_top : token list -> top option) tokens =
    do
      (ts,top) <- cmlParseREPLTop tokens;
      if ts <> [] then NONE else SOME top
    od
`;

val parse_prog_def = Define`
  parse_prog toks =
    do
      (toks',pts) <- destResult (cmlpegexec nTopLevelDecs toks);
      pt <- oHD pts;
      tds <- ptree_TopLevelDecs pt;
      if toks' <> [] then NONE else SOME tds
    od
`

(*
open lexer_funTheory;

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
