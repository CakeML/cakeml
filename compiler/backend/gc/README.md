This directory contains the garbage collector (GC) algorithms and
their verification proofs.

[copying_gcScript.sml](copying_gcScript.sml):
The straightforward non-generational copying garbage collector.

[gc_combinedScript.sml](gc_combinedScript.sml):
One function that can run any of the GC algorithms.

[gc_sharedScript.sml](gc_sharedScript.sml):
Types, functions and lemmas that are shared between GC definitions

[gen_gcScript.sml](gen_gcScript.sml):
The major collection of the generational copying garbage collector.

[gen_gc_partialScript.sml](gen_gc_partialScript.sml):
The minor collection of the generational copying garbage collector.
