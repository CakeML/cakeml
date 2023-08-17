(*
  Parser entry-point for the OCaml parser.
 *)

open preamble caml_lexTheory camlPEGTheory camlPtreeConversionTheory;
open mlintTheory mlstringTheory;

val _ = new_theory "caml_parser";

val _ = set_grammar_ancestry [
  "misc", "caml_lex", "camlPEG", "camlPtreeConversion",
  "mlstring", "mlint" ];

val _ = monadsyntax.temp_enable_monad "sum";

(* Run the lexer and return all tokens, or a list of all errors.
 *)

Definition run_lexer_def:
  run_lexer inp =
    let toks = lexer_fun inp;
        errs = MAP SND (FILTER (λ(tok,locs). tok = LexErrorT) toks)
    in if NULL errs then
      return toks
    else
      fail errs
End

Overload camlpegexec =
  “λn t. peg_exec camlPEG (pnt n) t [] NONE [] done failed”;

Definition destResult_def:
  destResult (Result (Success [] x eo)) =
    Success [] x eo ∧
  destResult (Result (Success ((_,l)::_) _ _)) =
    Failure l "Expected to be at EOF"  ∧
  destResult (Result (Failure fl fe)) =
    Failure fl fe ∧
  destResult _ =
    Failure unknown_loc "Something catastrophic happened"
End

Definition peg_def:
  peg (Failure locn err) = fail (locn, implode err) ∧
  peg (Success (_: (caml_lex$token # locs) list) x _) = return x
End

Definition run_parser_def:
  run_parser toks =
    do
      pt <- peg $ destResult $ camlpegexec nStart toks;
      case pt of
        [ptree] =>
          (case ptree_Start ptree of
            INR x => INR x
          | INL (loc, err) => fail (loc, err))
      | _ => fail (unknown_loc, «Impossible: run_parser»)
    od
End

Definition run_def:
  run inp =
    case run_lexer inp of
      INL locs => INL (HD locs, «LEXER ERROR»)
    | INR toks =>
        case run_parser toks of
          INL (loc, err) => INL (loc, err)
        | INR tree => INR tree
End

val _ = export_theory ();

