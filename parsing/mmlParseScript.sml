open HolKernel Parse boolLib bossLib

open mmlPEGTheory cmlPtreeConversionTheory pegSoundTheory
open lcsymtacs
open monadsyntax

local open mmlvalidTheory in end

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
    pt <- oHD pts;
    ast <- ptree_Expr nE pt;
    SOME(toks',ast)
  od
`;

val mmlParseREPLPhrase_def = Define`
  mmlParseREPLPhrase toks = do
    (toks', pts) <- destResult (mmlpegexec nREPLPhrase toks);
    pt <- oHD pts;
    ast <- ptree_REPLPhrase pt;
    SOME(toks',ast)
  od
`

(* to translate/eval mmlvalid, use theorems
     mmlvalidTheory.mml_okrule_eval_th
     mmlvalidTheory.mmlvalid_thm
     mmlvalidTheory.mmlvalidL_def
     grammarTheory.ptree_head_def

   mmlvalid and mmlvalidL are mutually recursive in this presentation.
*)

val mmlParseREPLTop_def = zDefine`
  mmlParseREPLTop doValidation toks = do
    (toks', pts) <- destResult (mmlpegexec nREPLTop toks);
    pt <- oHD pts;
    (* use if-then-else to hint at short-circuit/lazy evaluation *)
    assert(if doValidation then mmlvalid pt else T);
    ast <- ptree_REPLTop pt;
    SOME(toks',ast)
  od
`

val mmlpeg_executed =
    pegexecTheory.peg_eval_executed
      |> Q.GEN `G` |> Q.ISPEC `mmlPEG`
      |> SIMP_RULE (srw_ss()) [mmlPEGTheory.PEG_wellformed]
      |> Q.GEN `s` |> Q.GEN `r` |> Q.GEN `e` |> GSYM

val mmlParseREPLTop_thm = store_thm(
  "mmlParseREPLTop_thm",
  ``mmlParseREPLTop doV toks = do
      (toks', pts) <- destResult (mmlpegexec nREPLTop toks);
      pt <- oHD pts;
      ast <- ptree_REPLTop pt;
      SOME(toks',ast)
    od``,
  simp[mmlParseREPLTop_def] >>
  Cases_on `mmlpegexec nREPLTop toks` >> simp[destResult_def] >>
  Q.MATCH_ASSUM_RENAME_TAC `X = Result opt` ["X"] >> Cases_on `opt` >> simp[] >>
  Q.MATCH_ASSUM_RENAME_TAC `X = Result (SOME pair)` ["X"] >>
  `∃i r. pair = (i,r)` by (Cases_on `pair` >> simp[]) >> rw[] >>
  qspec_then `nt (mkNT nREPLTop) I`
    ((fn th => fs[th,pnt_def]) o SIMP_RULE (srw_ss()) [PEG_exprs,pnt_def])
    mmlpeg_executed >>
  pop_assum (strip_assume_tac o MATCH_MP peg_sound) >>
  simp[oHD_def, mmlvalidTheory.mmlvalid_def, gramTheory.assert_def,
       optionTheory.OPTION_IGNORE_BIND_def]);
val _ = computeLib.add_persistent_funs ["mmlParseREPLTop_thm"]

(* This function parses declarations, no junk is allowed at the end. *)
val parse_def = Define `
  (parse : token list -> ast_prog option) tokens =
    do
      (ts,ast_tdecs) <- mmlParseREPLPhrase tokens;
      if ts <> [] then NONE else SOME ast_tdecs
    od
`;

(* This function parses a single declaration followed by a semicolon.
   No junk is allowed at the end.
   It is used in implementation/repl_funScript.sml. *)
val parse_top_def = Define `
  (parse_top : token list -> ast_top option) tokens =
    do
      (ts,ast_top) <- mmlParseREPLTop T tokens;
      if ts <> [] then NONE else SOME ast_top
    od
`;

val _ = Hol_datatype`
  repl_parse_result = RPR_INCOMPLETE of token list
                    | RPR_PROG of ast_prog option => token list
`

val parse_REPLphrase_def = Define`
  parse_REPLphrase toks =
    do
      (toks',pts) <- destResult (mmlpegexec nREPLPhrase toks);
      pt <- oHD pts;
      tds <- ptree_REPLPhrase pt;
      SOME(toks',tds)
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
