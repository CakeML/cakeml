Prove the end-to-end correctness theorem for caketaiger.

[caketaigerProofScript.sml](caketaigerProofScript.sml):
Compose the semantics theorem and the compiler correctness
theorem with the compiler evaluation theorem to produce end-to-end
correctness theorem that reaches final machine code.

[caketaiger_lrupProofScript.sml](caketaiger_lrupProofScript.sml):
Compose the end-to-end correctness theorems of caketaiger and of the
verified LRUP checker cake_lrup: if caketaiger prints SUCCESS and cake_lrup
verifies each of the CNF files it wrote, then the input model is safe and
live.
