A verified compiler for CakeML, including:
 - lexing and PEG parsing,
 - type inference,
 - compilation to ASM assembly language, and,
 - code generation to x86, ARM, and more.

[backend](backend):
The CakeML compiler backend.

[benchmarks](benchmarks):
Two benchmark suites for the CakeML compiler.

[bootstrap](bootstrap):
Theories that perform proof-grounded bootstrapping of
the CakeML compiler in HOL.

[compilationLib.sml](compilationLib.sml):
Library for in-logic compilation of CakeML abstract syntax producing machine
code (for a variety of targets) using the CakeML compiler backend.

[compilerScript.sml](compilerScript.sml):
Definition of the CakeML compiler as a function that takes a list of command
line arguments and a string corresponding to standard input, and produces a
pair of output strings for standard error and standard output (the latter
containing the generated machine code if successful).

[dafny](dafny):
Translate Dafny into CakeML.

[encoders](encoders):
Encoders for CakeML's ASM abstract assembly language into each of the concrete
targets of the CakeML compiler.

[inference](inference):
The CakeML type inferencer.

[parsing](parsing):
The CakeML parser.

[printing](printing):
The printer mechanism for the CakeML REPL.

[proofs](proofs):
Correctness proof for the CakeML compiler.

[repl](repl):
Some definitions and proofs used in the proof of the CakeML
and Candle read-eval-print loop (REPL).
