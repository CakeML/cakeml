This directory contains a theorem stating that the compiler
configuration for the ARMv8 target is OK.

[arm8_targetProofLemmasScript.sml](arm8_targetProofLemmasScript.sml):
Lemmas used by arm8_targetProofLib. They are proved here, in a theory,
because proofs can no longer be run while a library is being loaded.

[arm8_targetProofLib.sml](arm8_targetProofLib.sml):
Various ML tools used in arm8_targetProofTheory.

[arm8_targetProofScript.sml](arm8_targetProofScript.sml):
Prove `encoder_correct` for ARMv8
