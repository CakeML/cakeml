(*
  Theorems and definitions to support adding runtime type checking annotations.
 *)
Theory runtime_check
Ancestors
  ml_translator holKernel mlstring
Libs
  preamble ml_translatorLib


Theorem pure_seq_intro:
  x = y ⇒ ∀z. x = pure_seq z y
Proof
  fs [pure_seq_def]
QED
