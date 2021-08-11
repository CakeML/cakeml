The Pancake compiler, i.e. a C-like compiler built from the lower
parts of the CakeML compiler.

[crepLangScript.sml](crepLangScript.sml):
Abstract syntax of Crepe language
Crepe: instrctuons are similar to that of
Pancake, but we flatten locals from
struct-layout to word-layout

[crep_to_loopScript.sml](crep_to_loopScript.sml):
Compilation from crepLang to panLang.

[example_prog.c](example_prog.c):
program for
 reading, preprocssing, writing,
 skipping until new characters are reached

[extra-files](extra-files):
Syntax for Pancake Language.

[ffi](ffi):
Definition of CakeML's observational semantics, in particular traces of calls
over the Foreign-Function Interface (FFI).

[loopLangScript.sml](loopLangScript.sml):
loopLang intermediate language

[loop_callScript.sml](loop_callScript.sml):
Call optimisation for loopLang

[loop_liveScript.sml](loop_liveScript.sml):
Correctness proof for loop to loop_remove

[loop_removeScript.sml](loop_removeScript.sml):
Correctness proof for loop_remove

[loop_to_wordScript.sml](loop_to_wordScript.sml):
Compilation from looLang to wordLang.

[panLangScript.sml](panLangScript.sml):
Abstract syntax for Pancake language.
Pancake is an imperative language with
instructions for conditionals, While loop,
memory load and store, functions,
and foreign function calls.

[pan_commonScript.sml](pan_commonScript.sml):
Common definitions for Pancake compiler

[pan_simpScript.sml](pan_simpScript.sml):
Compilation from panLang to crepLang.

[pan_to_crepScript.sml](pan_to_crepScript.sml):
Compilation from panLang to crepLang.

[pan_to_targetScript.sml](pan_to_targetScript.sml):
Compiler from Pancake to machine code

[pan_to_wordScript.sml](pan_to_wordScript.sml):
Compiler from pan to word

[proofs](proofs):
Proofs files for compiling Pancake.

[semantics](semantics):
Semantics for Pancake and its intermediate languages.

[taParserScript.sml](taParserScript.sml):
Parser for compactDSL programs

[ta_progs](ta_progs):
Some sample timed automata (TA) programs.

[timeLangScript.sml](timeLangScript.sml):
Abstract syntax for timeLang

[time_computationLib.sml](time_computationLib.sml):
Library for in-logic compilation of CakeML abstract syntax producing machine
code (for a variety of targets) using the CakeML compiler backend.

[time_evalScript.sml](time_evalScript.sml):
Evaluation of a timeLang program

[time_to_panScript.sml](time_to_panScript.sml):
Compilation from timeLang to panLang

[time_to_targetScript.sml](time_to_targetScript.sml):
Compiler from timeLang to machine code
