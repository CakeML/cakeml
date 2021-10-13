(*
  Parser entry-point for the OCaml parser.
 *)

open preamble caml_lexTheory camlPEGTheory camlPtreeConversionTheory;
open mlintTheory mlstringTheory;

val _ = new_theory "caml_parser";

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
          | INL (loc, err) =>
              fail (loc, concat [«Ptree conversion: »; err]))
      | _ => fail (unknown_loc, «Impossible: run_parser»)
    od
End

Definition locn_to_str_def:
  locn_to_str UNKNOWNpt = «an unknown point» ∧
  locn_to_str EOFpt = «the end of file» ∧
  locn_to_str (POSN r c) =
    concat [«row »; toString r; « and col »; toString c]
End

Definition locs_to_str_def:
  locs_to_str (Locs startl endl) =
    if Locs startl endl = unknown_loc then
      «unknown location»
    else
      concat [«between »; locn_to_str startl;
              « and »; locn_to_str endl]
End

(* These next few functions are taken directly from compilerScript.sml.
 *)

Definition find_next_newline_def:
  find_next_newline n s =
    if strlen s ≤ n then n else
      if strsub s n = #"\n" then n else
        find_next_newline (n+1) s
Termination
  WF_REL_TAC ‘measure (λ(n,s). strlen s - n)’
End

Definition safe_substring_def:
  safe_substring s n l =
    let k = strlen s in
      if k ≤ n then strlit "" else
        if n + l ≤ k then
          substring s n l
        else substring s n (k - n)
End

Definition get_nth_line_def:
  get_nth_line k s n =
    if k = 0 then
      let n1 = find_next_newline n s in
        safe_substring s n (n1 - n)
    else
      get_nth_line (k-1:num) s (find_next_newline n s + 1)
End

Definition locs_to_string_def:
  (locs_to_string input NONE = implode "unknown location") ∧
  (locs_to_string input (SOME (Locs startl endl)) =
    case startl of
    | POSN r c =>
       (let line = get_nth_line r input 0 in
        let len = strlen line in
        let stop =
          (case endl of POSN r1 c1 => (if r1 = r then c1 else len) | _ => len) in
        let underline =
          concat (REPLICATE c (strlit " ") ++ REPLICATE ((stop - c) + 1) (strlit [CHR 94])) in
          concat [strlit "line "; toString (r+1); strlit "\n\n";
                  line; strlit "\n";
                  underline;  strlit "\n"])
    | _ => implode "unknown location")
End

Definition run_def:
  run inp =
    case run_lexer inp of
      INL locs =>
        concat [«Lexing failed at: »;
                locs_to_string (implode inp) (SOME (HD locs))]
    | INR toks =>
        case run_parser toks of
          INL (loc, err) =>
            concat [«Parsing failed at: »;
                    locs_to_string (implode inp) (SOME loc);
                    «\nwith this error: »; err ]
        | INR tree =>
            «Parsing successful.»
End

val _ = export_theory ();

