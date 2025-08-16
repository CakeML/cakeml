Formalization of idealized semantics of FloVer that handle both real-numbered
semantics and finite-precision semantics.

Supported types are defined in `Infra/MachineTypesScript.sml`.

[AbbrevsScript.sml](AbbrevsScript.sml):
This file contains some type abbreviations, to ease writing.

[CommandsScript.sml](CommandsScript.sml):
Formalization of the Abstract Syntax Tree of a subset used in the Flover
framework

[ExpressionAbbrevsScript.sml](ExpressionAbbrevsScript.sml):
Some abbreviations that require having defined expressions beforehand
If we would put them in the Abbrevs file, this would create a circular
dependency

[ExpressionSemanticsScript.sml](ExpressionSemanticsScript.sml):
Formalization of the base expression language for the flover framework

[ExpressionsScript.sml](ExpressionsScript.sml):
Formalization of the base expression language for the flover framework

[FloverMapScript.sml](FloverMapScript.sml):
A simple Map datatype for FloVer, implement a version based on lists and one
based on trees
