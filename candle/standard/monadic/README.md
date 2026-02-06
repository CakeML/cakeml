Implementation of the Candle kernel as monadic functions in HOL (i.e. a
shallow embedding), and proof that they refine the HOL inference system.

The kernel implementation is heavily based on the HOL Light kernel.

[holKernelPmatchScript.sml](holKernelPmatchScript.sml):
This file proves alternative definitions of those HOL kernel
functions that have complex pattern matching. The new definitions
use PMATCH-based pmatch expressions instead of HOL's standard
per-datatype case constants.

[holKernelProofScript.sml](holKernelProofScript.sml):
Prove correctness of the monadic functions, i.e. prove that they are
faithful to the inference rules of the Candle logic.

[holKernelScript.sml](holKernelScript.sml):
Define the Candle kernel as shallowly embedded functions in HOL
using a monadic style in order to conveniently pass around state and
propagate exceptions.
