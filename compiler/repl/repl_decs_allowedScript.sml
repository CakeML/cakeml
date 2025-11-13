(*
  The REPL puts some restrictions on what decs are acceptable as user input.
  This file defines what those restrictions are.
*)
Theory repl_decs_allowed
Ancestors
  semanticsProps evaluate semanticPrimitives candle_prover_inv
Libs
  preamble

val _ = Parse.hide "types"

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* definition *)

Definition decs_allowed_def:
  decs_allowed (decs:ast$dec list) = EVERY candle_prover_inv$safe_dec decs
End

(* pmatch lemmas *)

Theorem safe_exp_pmatch_lemma[local]:
  safe_exp =
     every_exp $ λx. case x of
                     | Con opt xs => (dtcase opt of
                                      | SOME id => let n = id_to_n id in n ∉ kernel_ctors
                                      | NONE => T)
                     | App op xs' => op ≠ FFI kernel_ffi
                     | _ => T
Proof
  CONV_TAC(ONCE_DEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ rw [safe_exp_def,FUN_EQ_THM]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ rw [safe_exp_def,FUN_EQ_THM]
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []
QED

Theorem safe_exp_pmatch = safe_exp_pmatch_lemma
  |> SIMP_RULE std_ss [candle_kernel_valsTheory.kernel_ctors_def,
                       candle_kernel_valsTheory.kernel_ffi_def,
                       IN_UNION,IN_INSERT,NOT_IN_EMPTY,GSYM CONJ_ASSOC]

