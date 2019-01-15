A proof-producing translator from HOL functions to CakeML.

[ml_module_demoScript.sml](ml_module_demoScript.sml):
Demonstration of using the translator to produce a CakeML module.

[ml_optimiseScript.sml](ml_optimiseScript.sml):
A simple verified optimiser for CakeML expressions, which is applied once the
translator has produced some CakeML syntax.

[ml_pmatchScript.sml](ml_pmatchScript.sml):
Theory support for translation of deeply-embedded (PMATCH-based)
pattern-matches occurring in HOL functions.

[ml_pmatch_demoScript.sml](ml_pmatch_demoScript.sml):
Demonstration of using the translator on functions containing PMATCH-based
pattern matching.

[ml_progComputeLib.sml](ml_progComputeLib.sml):
compset for the definitions in ml_progTheory.

[ml_progLib.sml](ml_progLib.sml):
Functions for constructing a CakeML program (a list of declarations) together
with the semantic environment resulting from evaluation of the program.

[ml_progScript.sml](ml_progScript.sml):
Definitions and theorems supporting ml_progLib, which constructs a
CakeML program and its semantic environment.

[ml_translatorLib.sml](ml_translatorLib.sml):
The HOL to CakeML translator itself.
The main entry point is the translate function.

[ml_translatorScript.sml](ml_translatorScript.sml):
This script defines Eval and other core definitions used by the
translator. The theorems about Eval serve as an interface between
the source semantics and the translator's automation.

[ml_translatorSyntax.sml](ml_translatorSyntax.sml):
Library for manipulating the HOL terms and types defined in
ml_translatorTheory.

[ml_translator_demoScript.sml](ml_translator_demoScript.sml):
A small example of using the HOL to CakeML translator.

[ml_translator_testScript.sml](ml_translator_testScript.sml):
A collection of functions that have in the past turned out to be tricky to
translate.

[ml_translator_word_testScript.sml](ml_translator_word_testScript.sml):
Tests of word operation translation

[monadic](monadic):
Extensions to the proof-producing translator to support
stateful/imperative (monadic) HOL functions.

[okasaki-examples](okasaki-examples):
Examples of using the CakeML translator on functional programs based on the
algorithms in "Purely Functional Data Structures" by Chris Okasaki (1996).

[other-examples](other-examples):
A few other examples of HOL functions that can be translated into CakeML.

[std_preludeScript.sml](std_preludeScript.sml):
Translations of various useful HOL functions and datatypes, to serve as a
starting point for further translations.
