Main implementation directory for the RealCake development, presented in
"Verified Compilation and Optimization of Floating-Point Programs"

===========================================================================

Content in the directory can be build with `Holmake`.

Files contained in this directory:

[CakeMLtoFloVerLemsScript.sml](CakeMLtoFloVerLemsScript.sml):
Lemmas for connection to FloVer,
the translation function is defined in CakeMLtoFloVerScript.sml, and the main
connection theorem in CakeMLtoFloVerProofsScript.sml

[CakeMLtoFloVerProofsScript.sml](CakeMLtoFloVerProofsScript.sml):
Main connection theorem relating FloVer's roundoff error bound
to CakeML floating-point kernel executions

[CakeMLtoFloVerScript.sml](CakeMLtoFloVerScript.sml):
Translation from CakeML floating-point kernels to FloVer input

[cfSupportScript.sml](cfSupportScript.sml):
Support lemmas for CF proofs in the end-to-end correctness theorems

[examples](examples):
FPBench benchmarks used in the evaluation of PrincessCake.

[floatToRealProofsScript.sml](floatToRealProofsScript.sml):
Proofs about translation from floating-point computations to real-number
computations. Needed to prove simulations in the end-to-end correctness
theorems.

[floatToRealScript.sml](floatToRealScript.sml):
Translation from CakeML floating-point computations to
CakeML real-number computations.

[flover](flover):
# FloVer - A Certificate Checker for Roundoff Error Bounds

[icingTacticsLib.sml](icingTacticsLib.sml):
Tactic library for PrincessCake development

[icing_optimisationProofsScript.sml](icing_optimisationProofsScript.sml):
Correctness proofs for peephole optimisations supported by PrincessCake
Each optimisation is defined in icing_optimisationsScript.sml.
This file proves the low-level correctness theorems for a single
application of the optimisation.
Real-valued identity proofs are in icing_realIdProofsScript.sml.
The overall correctness proof for a particular run of the optimiser
from source_to_source2Script is build using the automation in
icing_optimisationsLib and the general theorems from
source_to_source2ProofsScript.

[icing_optimisationsLib.sml](icing_optimisationsLib.sml):
Library defining HOL4 automation that builds an optimiser
correctness theorem for an optimisation plan.

[icing_optimisationsScript.sml](icing_optimisationsScript.sml):
Peephole optimisations used by PrincessCake
This file defines all the optimisations that are can be used by the
PrincessCake optimiser, defined in source_to_source2Script.sml .
The local correctness proofs for each optimisation are in the file
icing_optimisationProofsScript.

[icing_realIdProofsScript.sml](icing_realIdProofsScript.sml):
Real-number identity proofs for Icing optimisations supported by CakeML
Each optimisation is defined in icing_optimisationsScript.
This file proves that optimisations  are real-valued identities.
The overall real-number simluation proof for a particular run of the optimiser
from source_to_source2Script is build using the automation in
icing_optimisationsLib and the general theorems from
source_to_source2ProofsScript.

[icing_rewriterProofsScript.sml](icing_rewriterProofsScript.sml):
Correctness proofs for the expression rewriting function
Shows that matchesExpr e p = SOME s ==> appExpr p s = SOME e

[icing_rewriterScript.sml](icing_rewriterScript.sml):
Implementation of the source to source floating-point rewriter
This file defines the basic rewriter, used by the optimisation pass later.
Correctness proofs are in icing_rewriterProofsScript.

[new_backendProofScript.sml](new_backendProofScript.sml):
Proof of a new overall compiler correctness theorem for
the global constant lifting, showing that it is semantics preserving

[optPlannerProofsScript.sml](optPlannerProofsScript.sml):
Correctness proof for optimization planner

[optPlannerScript.sml](optPlannerScript.sml):
Unverified optimisation planner.
Definitions in this file correspond to the function ‘planOpts’
from Section 5 of the PrincessCake paper.

[pull_wordsScript.sml](pull_wordsScript.sml):
Implementation and correctness proof of the global constant lifting
(Section 7.2)

[pureExpsScript.sml](pureExpsScript.sml):
Implements a predicate to check whether an expression is pure, i.e. does not
use memory or the FFI

[source_to_source2ProofsScript.sml](source_to_source2ProofsScript.sml):
Overall correctness proofs for optimisation functions
defined in source_to_source2Script.sml.
To prove a particular run correct, they are combined
using the automation in icing_optimisationsLib.sml with
the local correctness theorems from icing_optimisationProofsScript.sml.

[source_to_source2Script.sml](source_to_source2Script.sml):
This file defines the PrincessCake optimiser as a source to source pass.
Function ‵stos_pass_with_plans‵ corresponds to ‵applyOpts‵
from the paper.
General correctness theorems are proven in source_to_sourceProofsScript.
The optimiser definitions rely on the low-level functions from
icing_rewriterScript implementing pattern matching and pattern instantiation.

[supportLib.sml](supportLib.sml):
Library defining commonly used functions for Icing integration
