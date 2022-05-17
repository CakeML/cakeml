(*
  Pmatch definitions for functions in computeScript.sml.
 *)

open preamble computeTheory;
local open patternMatchesLib in end;

val _ = new_theory "computePmatch";

val _ = numLib.prefer_num ();

val _ = patternMatchesLib.ENABLE_PMATCH_CASES ();

Theorem dest_num_PMATCH:
  ∀tm.
    dest_num tm =
      case tm of
        Const n t => if tm = _0 then SOME 0 else NONE
      | Comb (Const nm t) r =>
          (dtcase dest_num r of
          | NONE => NONE
          | SOME n => if Const nm t = _BIT0_TM then SOME (2 * n)
                      else if Const nm t = _BIT1_TM then SOME (2 * n + 1)
                      else NONE)
      | _ => NONE
Proof
  CONV_TAC (DEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ rw [Once dest_num_def]
QED

Theorem dest_numeral_PMATCH:
  ∀tm.
    dest_numeral tm =
      case tm of
        Comb (Const n t) r =>
          if Const n t = _NUMERAL_TM then
            dtcase dest_num r of
            | NONE => raise_Failure «dest_numeral»
            | SOME n => st_ex_return n
          else
            raise_Failure «dest_numeral»
      | _ => raise_Failure «dest_numeral»
Proof
  rw [Once dest_numeral_def]
  \\ CONV_TAC (DEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV) \\ rw []
QED

Theorem dest_binary_PMATCH:
  ∀tm' tm.
    dest_binary tm' tm =
      case tm of
        Comb (Comb (Const n t) l) r =>
          if tm' = Const n t then st_ex_return (l, r)
          else raise_Failure «dest_binary»
      | _ => raise_Failure «dest_binary»
Proof
  CONV_TAC (DEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ rw [Once dest_binary_def]
QED

Theorem dest_numeral_opt_PMATCH:
  ∀tm.
    dest_numeral_opt tm =
      case tm of
        Comb (Const n t) r =>
          if Const n t = _NUMERAL_TM then
            dtcase dest_num r of
            | NONE => NONE
            | SOME n => SOME n
          else
            NONE
      | _ => NONE
Proof
  rw [Once dest_numeral_opt_def]
  \\ CONV_TAC (DEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV) \\ rw []
QED

val _ = export_theory ();

