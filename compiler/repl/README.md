Some definitions and proofs used in the proof of the CakeML
and Candle read-eval-print loop (REPL).

[evaluate_skipScript.sml](evaluate_skipScript.sml):
Lemmas used in repl_typesTheory. These lemmas show that a plain
evaluate run can be replicated in a state with junk refs, extra type
stamps and unused exception definitions.

[repl_check_and_tweakScript.sml](repl_check_and_tweakScript.sml):
The REPL type checks and modifies the decs given as input. This file
defines the function that implements this and proves that the
function will only produce type checked and allowed declarations.

[repl_decs_allowedScript.sml](repl_decs_allowedScript.sml):
The REPL puts some restrictions on what decs are acceptable as user input.
This file defines what those restrictions are.

[repl_initScript.sml](repl_initScript.sml):
Proves repl_types for the initial env and types from which the REPL starts.

[repl_init_envProgScript.sml](repl_init_envProgScript.sml):
This file partially instantiates the eval_state and inserts a Denv declaration.

[repl_init_typesScript.sml](repl_init_typesScript.sml):
This file runs the type inferencer on the declarations of the basis,
Candle kernel and REPL module, i.e. everything in the user-visible
initial environment of the read-eval-print loop.

[repl_moduleProgScript.sml](repl_moduleProgScript.sml):
Module for the configurable part of the REPL. Note that this file
does not contain the code for the main loop of the REPL (which is at
the end of bootstrap translation).

[repl_typesScript.sml](repl_typesScript.sml):
Proofs about how the REPL uses types and the type inferencer
