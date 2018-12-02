A verified CakeML adaption of Arthur Charguéraud's "Characteristic
Formulae for the Verification of Imperative Programs"

[cfAppLib.sml](cfAppLib.sml):
Defines app_of_Arrow_rule function that converts the translator's
Arrow to CF's app judgement.

[cfAppScript.sml](cfAppScript.sml):
App: [app] is used to give a specification for the application of a
value to one or multiple value arguments. It is in particular used
in cf to abstract from the concrete representation of closures.

[cfAppSyntax.sml](cfAppSyntax.sml):
Helper functions that construct/destruct syntax from cfAppTheory.

[cfComputeLib.sml](cfComputeLib.sml):
Auxiliary definitions used in cfs

[cfDivScript.sml](cfDivScript.sml):
Defines the repeat function and the corresponding lemma used to prove
non-termination of programs in cf.

[cfFFITypeScript.sml](cfFFITypeScript.sml):
Defines a type that can be used for embedding different FFI models
for parts of the FFI state.

[cfHeapsBaseLib.sml](cfHeapsBaseLib.sml):
Implements CF tactics for CF-style separation logic

[cfHeapsBaseScript.sml](cfHeapsBaseScript.sml):
Defines the heap type that the separation logic used by CF uses.
Also defines POSTv etc.

[cfHeapsBaseSyntax.sml](cfHeapsBaseSyntax.sml):
Functions that aid in dealing with syntax of CF-style separation logic.

[cfHeapsLib.sml](cfHeapsLib.sml):
Conversions etc. over hprops

[cfHeapsScript.sml](cfHeapsScript.sml):
Defines what is means for a CF separation logic assertion to be "local".

[cfLetAutoLib.sml](cfLetAutoLib.sml):
Theorems, conversions, solvers used by the xlet_auto tactic.

[cfLetAutoScript.sml](cfLetAutoScript.sml):
Definitions and lemmas that support the implementation of the
xlet_auto tactic.

[cfLib.sml](cfLib.sml):
This library collects all CF-related libraries and theories
into a single import for convenience.

[cfMainScript.sml](cfMainScript.sml):
The following section culminates in call_main_thm2 which takes a
spec and some aspects of the current state, and proves a
Semantics_prog statement.

[cfNormaliseLib.sml](cfNormaliseLib.sml):
Automation that normalises a CakeML program. In particular, this
means turning it into A-normal form.

[cfNormaliseScript.sml](cfNormaliseScript.sml):
Defines the normalise_prog function which puts an arbitrary program
in A-normal form.

[cfScript.sml](cfScript.sml):
Defines the characteristic formula (CF) function cf_def and proves
that it is sound w.r.t. the evaluate semantics of CakeML.

[cfStoreScript.sml](cfStoreScript.sml):
Conversion from semantic stores to heaps.

[cfSyntax.sml](cfSyntax.sml):
Helper functions for syntax from cfTheory.

[cfTacticsBaseLib.sml](cfTacticsBaseLib.sml):
Various tactics for reasoning about CF-based goals in HOL.

[cfTacticsLib.sml](cfTacticsLib.sml):
Various tactics for reasoning about CF-based goals in HOL.

[cfTacticsScript.sml](cfTacticsScript.sml):
Lemmas that aid the tactics for reasoning about CF-based goals in HOL.

[eqSolveRewriteLib.sml](eqSolveRewriteLib.sml):
Defines ELIM_UNKWN_CONV conversion

[evarsConseqConvLib.sml](evarsConseqConvLib.sml):
Some experimental code for emulating evars support in HOL.

[examples](examples):
This directory contains examples of how the CF tactics can be used.
