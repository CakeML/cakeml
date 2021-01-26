Icing: CAV'19...

[CakeMLtoFloVerLemsScript.sml](CakeMLtoFloVerLemsScript.sml):
Lemmas for connection to FloVer

[CakeMLtoFloVerProofsScript.sml](CakeMLtoFloVerProofsScript.sml):
Central theorem about connection to FloVer

[CakeMLtoFloVerScript.sml](CakeMLtoFloVerScript.sml):
Definition of translation to FloVer

[cfSupportScript.sml](cfSupportScript.sml):
Support lemmas for CF reasoning

[examples](examples):
Case studies for the Marzipan optimizer

[icing_optimisationProofsScript.sml](icing_optimisationProofsScript.sml):
Correctness proofs for Icing optimisations supported by CakeML
Each optimisation is defined in icing_optimisationsScript.
This file proves the low-level correctness theorems for a single
application of the optimisation, as well as that optimisations
are real-valued identities.
The overall correctness proof for a particular run of the optimiser
from source_to_sourceScript is build using the automation in
icing_optimisationsLib and the general theorems from
source_to_sourceProofsScript.

[icing_optimisationsLib.sml](icing_optimisationsLib.sml):
Library defining function mk_opt_correct_thms that builds an optimiser
correctness theorem for a list of rewriteFPexp_correct theorems

[icing_optimisationsScript.sml](icing_optimisationsScript.sml):
Icing optimisations supported by CakeML
This file defines all the optimisations that can be used by the Icing
optimizer, defined in source_to_sourceScript.
Correctness proofs for each optimisation are in the file
icing_optimisationProofsScript.

[icing_rewriterProofsScript.sml](icing_rewriterProofsScript.sml):
Correctness proofs for the expression rewriting function
Shows that matchesExpr e p = SOME s ==> appExpr p s = SOME e

[icing_rewriterScript.sml](icing_rewriterScript.sml):
Implementation of the source to source floating-point rewriter
This file defines the basic rewriter, used by the optimisation pass later.
Correctness proofs are in icing_rewriterProofsScript.

[source_to_sourceProofsScript.sml](source_to_sourceProofsScript.sml):
Correctness proofs for floating-point optimizations

[source_to_sourceScript.sml](source_to_sourceScript.sml):
Source to source optimiser, applying Icing optimizations
This file defines the high-level Icing optimisers.
Their general correctness theorems are proven in source_to_sourceProofsScript.
The optimiser definitions rely on the low-level functions from
icing_rewriterScript implementing pattern matching and pattern instantiation.

[supportLib.sml](supportLib.sml):
Library defining commonly used functions for Icing integration
