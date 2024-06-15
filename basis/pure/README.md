HOL definitions of the pure functions used in the CakeML basis.

The CakeML code for the pure parts of the basis is produced
from these by the translator.

[basisComputeLib.sml](basisComputeLib.sml):
compset for the pure basis functions.

[basis_cvScript.sml](basis_cvScript.sml):
Translation of basis types and functions for use with cv_compute.

[mlintScript.sml](mlintScript.sml):
Pure functions for the Int module.

[mllistScript.sml](mllistScript.sml):
Pure functions for the List module.

[mlmapScript.sml](mlmapScript.sml):
Pure functions for the Map module.
This file defines a wrapper around the balanced_map type. The new
type is essentially a pair that carries the compare functions next
to the tree so that users don't have to provide the compare function
as an explicit argument everywhere.

[mloptionScript.sml](mloptionScript.sml):
Pure functions for the Option module.

[mlprettyprinterScript.sml](mlprettyprinterScript.sml):
Types and pure functions for pretty printing

[mlratScript.sml](mlratScript.sml):
Pure functions for the Rat module.

[mlstringLib.sml](mlstringLib.sml):
More ML functions for manipulating HOL terms involving mlstrings.

[mlstringScript.sml](mlstringScript.sml):
Pure functions for the String module.

[mlstringSyntax.sml](mlstringSyntax.sml):
ML functions for manipulating HOL terms and types involving mlstrings.

[mlvectorScript.sml](mlvectorScript.sml):
Pure functions for the Vector module.

[mlvectorSyntax.sml](mlvectorSyntax.sml):
ML functions for manipulating HOL terms and types involving vectors.

[typeDecToPPScript.sml](typeDecToPPScript.sml):
Maps a Dtype or Dtabbrev declaration (the ast syntax) to
the default pretty-printer function definition for it
(also as ast syntax).
