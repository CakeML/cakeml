Verification of a HOL theorem prover, based on HOL Light
(http://www.cl.cam.ac.uk/~jrh13/hol-light/), implemented in CakeML.

[overloading](overloading):
Definition of the inference system for HOL with ad-hoc overloading,
including semantics in set theory and proofs of soundness and
consistency.

[parser](parser):
The parser for Candle's OCaml-like syntax, written in CakeML. `cake --candle`
loads `candle_boot.cml`, which is this directory's parser sources followed by
`candle_glue.cml`; Candle input then reaches the verified REPL as parsed
declarations. The parser is a port of the definitions in
`compiler/parsing/ocaml`.

[prover](prover):
Proof of soundness for the Candle theorem prover.

[set-theory](set-theory):
A specification of (roughly) Zermelo's set theory.

[standard](standard):
Definition of the inference system for HOL, including semantics in set theory
and proofs of soundness and consistency.

[syntax-lib](syntax-lib):
Auxiliary definitions used for manipulating (deeply embedded) HOL syntax.
