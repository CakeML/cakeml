Various unverified tools, e.g. tools for converting OCaml to CakeML
and an SML version of the CakeML register allocator.

[benchmarks](benchmarks):
One benchmark. TODO: delete?

[front-end](front-end):
A CakeML front-end written in Haskell. It tries to give reasonable parse and
type error messages that include source locations. It includes a rudimentary
CakeML to OCaml and CakeML to SML translator, currently used for benchmarking.

[hol-light-syntax](hol-light-syntax):
A work in progress attempt to translate the particular OCaml syntax used by HOL
Light into Standard ML (as a step towards CakeML).

[ocaml-syntax](ocaml-syntax):
An OCaml to CakeML translator. Possibly translates type-correct OCaml files to
equivalent CakeML files.

[reg_alloc](reg_alloc):
A snapshot of the register allocator from the CakeML compiler, translated from
HOL to CakeML then pretty-printed in Standard ML syntax.

[sexpr-bootstrap](sexpr-bootstrap):
An alternative bootstrapping process: The translated AST of the compiler is
printed as an S-expression then fed into a previously built executable of the
CakeML compiler.
