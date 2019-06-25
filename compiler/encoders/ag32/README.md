This directory contains the definition of the instruction encoder and
compiler configuration for Silver.

[ag32Script.sml](ag32Script.sml):
An instruction set model generated from Anthony Fox's L3 tool.
[ag32_targetLib.sml](ag32_targetLib.sml):
A compset for evaluating the ag32 instruction encoder and config.

[ag32_targetScript.sml](ag32_targetScript.sml):
Define the target compiler configuration for ag32.

[proofs](proofs):
This directory contains a theorem stating that the compiler
configuration for the Silver target is OK.
