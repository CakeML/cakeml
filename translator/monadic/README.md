Extensions to the proof-producing translator to support
stateful/imperative (monadic) HOL functions.

[cfMonadLib.sml](cfMonadLib.sml):
Automation that converts between judgements used by CF and
judgements used by the monadic translator.

[cfMonadScript.sml](cfMonadScript.sml):
Proves a connection between the monadic translator's ArrowP
judgement and CF's app judgement.

[examples](examples):
This directory contains example applications of the monadic translator.
These examples serve as test cases of the monadic translator.

[ml_monadStoreLib.sml](ml_monadStoreLib.sml):
Automation that derives lemmas about arrays and references for use
by the monadic translator.

[ml_monadStoreScript.sml](ml_monadStoreScript.sml):
This file defines theorems and lemma used in the ml_monadStoreLib

[ml_monad_translatorBaseScript.sml](ml_monad_translatorBaseScript.sml):
Assertions about references and arrays are defined. Lemmas for these
are proved, including reasoning in separation logic.

[ml_monad_translatorLib.sml](ml_monad_translatorLib.sml):
The ML code that implements the main part of the monadic translator.

[ml_monad_translatorScript.sml](ml_monad_translatorScript.sml):
Defines EvalM and other judgements that are central to the monadic
translator.

[ml_monad_translator_interfaceLib.sml](ml_monad_translator_interfaceLib.sml):
The user-friendly interface to the monadic translator

[monad_base](monad_base):
The state-and-exception monad that is used by the proof-producing translator
for monadic HOL functions.
