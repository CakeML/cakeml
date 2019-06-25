The CakeML type inferencer.

[inferScript.sml](inferScript.sml):
Definition of CakeML's type inferencer.

[infer_tScript.sml](infer_tScript.sml):
The infer_t datatype and various to_string functions.

[inferenceComputeLib.sml](inferenceComputeLib.sml):
A compset for the type inferencer. This is to make it easy to
evaluate the type inferencers inside the logic. See tests.

[proofs](proofs):
This directory contains the correctness proofs for the type
inferencer: both soundness and completeness proofs.

[tests](tests):
This directory contains tests that evaluate the type inferencer inside
the logic of HOL.

[unifyLib.sml](unifyLib.sml):
Code that makes evaluating the unification algorithm easy.

[unifyScript.sml](unifyScript.sml):
Defines a unification algorithm for use in the type inferencer.
Based on the triangular unification algorithm in
HOL/examples/unification/triangular/first-order.  We encode our
CakeML types into the term structure used there and them bring over
those definitions and theorems.
