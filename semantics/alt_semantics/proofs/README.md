The direcory contains proofs about the old relational semantics for
CakeML. This directory might be deleted in the future.

[bigClockScript.sml](bigClockScript.sml):
Theorems about the clocked big-step semantics. Primarily that they
are total, and that they have the proper relationship to the
unclocked version.

[bigSmallEquivScript.sml](bigSmallEquivScript.sml):
Big step/small step equivalence

[bigSmallInvariants.lem](bigSmallInvariants.lem):
Invariants used in the proof relating the big-step and small-step
version of the CakeML source semantics.

[bigStepPropsScript.sml](bigStepPropsScript.sml):
A few properties about the relational big-step semantics.

[determScript.sml](determScript.sml):
Determinism for the big-step semantics

[funBigStepEquivScript.sml](funBigStepEquivScript.sml):
Relate functional big-step semantics with relational big-step
semantics.

[interpComputeLib.sml](interpComputeLib.sml):
Compset for evaluating the functional big-step semantics.

[interpScript.sml](interpScript.sml):
A functional big-step semantics.

[untypedSafetyScript.sml](untypedSafetyScript.sml):
Prove that the small step semantics never gets stuck if there is
still work to do (i.e., it must detect all type errors).  Thus, it
either diverges or gives a result, and it can't do both.
