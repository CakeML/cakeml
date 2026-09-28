Prove the end-to-end correctness theorem for cake_tiger.

[cake_tigerProofScript.sml](cake_tigerProofScript.sml):
Compose the semantics theorem and the compiler correctness
theorem with the compiler evaluation theorem to produce end-to-end
correctness theorem that reaches final machine code.

[cake_tiger_lrupProofScript.sml](cake_tiger_lrupProofScript.sml):
Compose the end-to-end correctness theorems of cake_tiger and of the
verified LRUP checker cake_lrup: if cake_tiger prints SUCCESS and cake_lrup
verifies each of the CNF files it wrote, then the input model is safe and
live.
