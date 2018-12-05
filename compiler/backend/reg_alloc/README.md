This directory contains the implementation of the register allocator
and parallel-move algorithms.

[linear_scanScript.sml](linear_scanScript.sml):
A linear-scan register allocator.

[parmoveScript.sml](parmoveScript.sml):
Compiling parallel moves.
This is a formalisation of a JAR'08 paper by Rideau, Serpette, Leroy:
  Tilting at windmills with Coq: formal verification of a compilation
  algorithm for parallel moves
http://gallium.inria.fr/~xleroy/publi/parallel-move.pdf

[proofs](proofs):
This directory contains the proofs of the register allocator and
parallel-move algorithms.

[reg_allocComputeLib.sml](reg_allocComputeLib.sml):
A compset for evaluating the register allocators and parallel move
compiler.

[reg_allocScript.sml](reg_allocScript.sml):
A monadic graph-coloring register allocator
