Some definitions and proofs used in the proof of the CakeML
and Candle read-eval-print loop (REPL).

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
