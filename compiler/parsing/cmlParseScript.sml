(*
  Definition of the overall parsing functions that go from tokens to abstract
  syntax trees. In other words, these include calls to the functions in
  `../semantics/cmlPtreeConversion`.
*)
Theory cmlParse
Ancestors
  cmlPEG cmlPtreeConversion


val _ = monadsyntax.temp_add_monadsyntax()

Overload cmlpegexec = ``λn t. peg_exec cmlPEG (pnt n) t [] NONE [] done failed``

Definition destResult_def:
  destResult (Result (Success [] x eo)) = Success [] x eo ∧
  destResult (Result (Success ((_,l)::_) _ _)) =
  Failure l "Expected to be at EOF" ∧
  destResult (Result (Failure fl fe)) = Failure fl fe ∧
  destResult _ = Failure unknown_loc "Something catastrophic happened"
End

Type M[local,pp] = “:(token # locs) list -> ((token # locs) list, α, string) pegresult”
Definition pegresult_bind_def:
  pegresult_bind (f:α M) (g:α -> β M) : β M =
  λtoks.
    case f toks of
      Success toks' x eo => g x toks'
    | Failure fl fe => Failure fl fe
End

Definition pegresult_choice_def:
  pegresult_choice (f : α M) (g : α M) : α M =
  λtoks.
    case f toks of
      Success toks' x eo => Success toks' x eo
    | _ => g toks
End

Definition toks_to_loc_def:
  toks_to_loc [] = unknown_loc ∧
  toks_to_loc ((h,L) :: _ ) = L
End

Definition pegresult_guard_def:
  pegresult_guard b : unit M =
  λtoks. if b then Success toks () NONE
         else Failure (toks_to_loc toks) "Assert failure"
End

val _ = monadsyntax.declare_monad (
  "pegresult",
  {bind = “pegresult_bind”,
   choice = SOME “pegresult_choice”,
   fail = SOME “K (Failure unknown_loc "Unknown error") : α M”,
   guard = SOME“pegresult_guard”,
   ignorebind = NONE,
   unit = “λa inp. Success inp a NONE”})
val _ = monadsyntax.temp_enable_monad "pegresult"

Definition optlift_def:
  optlift NONE : α M = (λtoks. Failure (toks_to_loc toks) "Option = NONE") ∧
  optlift (SOME a) = λtoks. Success toks a NONE
End

Definition cmlParseExpr_def:
  cmlParseExpr = do
    pts <- destResult o cmlpegexec nE;
    pt <- optlift $ oHD pts;
    ast <- optlift $ ptree_Expr nE pt;
    return ast
  od
End

Definition parse_prog_def:
  parse_prog =
    do
      pts <- destResult o cmlpegexec nTopLevelDecs;
      pt <- optlift $ oHD pts;
      optlift $ ptree_TopLevelDecs pt;
    od
End

