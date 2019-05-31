The CakeML compiler backend.

[ag32](ag32):
This directory contains the Silver-specific part of the compiler
backend and associated proofs.

[arm7](arm7):
This directory contains the ARMv7-specific part of the compiler backend.

[arm8](arm8):
This directory contains the ARMv8-specific part of the compiler backend.

[backendComputeLib.sml](backendComputeLib.sml):
A compset for evaluating the compiler backend inside the logic of HOL.

[backendScript.sml](backendScript.sml):
Composes all of the compiler phases within the compiler backend into
a single compile function which is connected (in ../compilerScript.sml)
to the front-end, i.e. parsing and type inference.

[backend_commonScript.sml](backend_commonScript.sml):
Definitions that are common for many parts of the compiler backend.

[bviScript.sml](bviScript.sml):
The BVI intermediate language. This language is very similar to BVL.
One of the more notable differences is that exception handling is
now bundled together with function calls: exceptions can only be
caught at the point of function calls.

[bvi_letScript.sml](bvi_letScript.sml):
This is a BVI transformation that propagates variable lookups that
are immediately assigned to a new variable in Let bindings. This
optimisation is to run immediately when entering BVI.

[bvi_tailrecScript.sml](bvi_tailrecScript.sml):
A compiler phase that turns some non-tail-recursive functions into
tail-recursive functions.

[bvi_to_dataScript.sml](bvi_to_dataScript.sml):
A compiler phase that turns programs of the functional language BVI
into the first imperative language of the CakeML compiler: dataLang.

[bvlScript.sml](bvlScript.sml):
The BVL intermediate language. This language is a simple first-order
functional language without closures.

[bvl_constScript.sml](bvl_constScript.sml):
This is a BVL transformation that propagates simple and
cheap-to-compute context-free expression from Let bindings. It also
performs some simple constant folding with SmartOp (below).

[bvl_handleScript.sml](bvl_handleScript.sml):
BVL transformation that introduces a Let into each Handle
body. This is preparation for BVL --> BVI compilation.  This phase
also removes Handles in case the body cannot raise an exception.

[bvl_inlineScript.sml](bvl_inlineScript.sml):
A simple function-inlining optimisation within the BVL language.
There is a more advanced inlining optimisation as part of
clos_known.

[bvl_jumpScript.sml](bvl_jumpScript.sml):
A function for generating efficient switch-like jumps in BVL.

[bvl_to_bviScript.sml](bvl_to_bviScript.sml):
A compiler phases that transforms BVL programs into BVI programs. As
part of this phase, certain primitive operations map to "stubs" code
implemented in BVI; numeric constants are split into smaller ones to
ease code generation later; Handle is fused with Call; and very
large expressions are split into samller ones (in order to protect
the register allocator from overly large inputs).

[closLangScript.sml](closLangScript.sml):
The closLang intermediate language. This language is the last
intermediate language that has closure values. This language is
designed for optimisation of function calls.

[clos_annotateScript.sml](clos_annotateScript.sml):
A compiler phase that annotates code that creates closures with
(minimal) live variable annotations. Such live variable annotations
are required for closure conversion, which is implemented in
the clos_to_bvl phase of the compiler.

[clos_callScript.sml](clos_callScript.sml):
This compiler phase moves code from closures into a separate code
table and tries to change calls to known closures into fast C-style
function calls.

[clos_fvsScript.sml](clos_fvsScript.sml):
Replaces free variables with constant type errors.

[clos_knownScript.sml](clos_knownScript.sml):
This complicated compiler phase tracks where closure values flow
in a program. It attempts to annotate function applications with the
(numeric) names of the called closures (annotations lead to better
code in clos_to_bvl). If the code for the applied closure is
statically known and small enough, then this compiler phase can
inline the body of the called closure. The function inlining is
recurisve and controlled using configurable parameters.

[clos_labelsScript.sml](clos_labelsScript.sml):
Replaces calls to unknown functions with constant type errors.

[clos_letopScript.sml](clos_letopScript.sml):
This simple compiler phase tidies up after function inlining, in
particular it turns `Let [x0; x1; ...] (Op op [Var 0; Var 1; ...])`
into `Op op [x0; x1; ...]`, which enables further optimisation
later, e.g. in bvi_tailrec.

[clos_mtiScript.sml](clos_mtiScript.sml):
This compiler phase introduces multi-argument function applications
and function closures. This phase enables subsequent compiler phases
to make use of closLang's support for true multi-argument
functions. This phase is vital for good performance.

[clos_numberScript.sml](clos_numberScript.sml):
This simple compiler phase walks the program and gives each closure
a unique numeric name.

[clos_ticksScript.sml](clos_ticksScript.sml):
This simple compiler phase removes all Tick operations. Tick
operations appear as a side effect of function inlining, and can be
removed because they have no observable behaviour. It is good idea
to remove them because they get in the way of pattern matching done
by several optimisations.

[clos_to_bvlScript.sml](clos_to_bvlScript.sml):
This compiler phase performs closure conversion.  This phase puts
all of the code into a table of first-order, closed, multi-argument
functions.

[dataLangScript.sml](dataLangScript.sml):
The dataLang intermediate lannguage is the last language with a
functional-programming-style data abstraction.

[data_liveScript.sml](data_liveScript.sml):
This compiler phase minimises the live-var annotations that are
attached to MakeSpace, Assign and Call in dataLang programs. This
phase also locally deletes code that has no observable effect.

[data_simpScript.sml](data_simpScript.sml):
This simple compiler phase cleans up dataLang programs.  The simp
optimisation removes Skips and deletes some dead code created by
Raise and Return.

[data_spaceScript.sml](data_spaceScript.sml):
This dataLang phase lumps together MakeSpace operations. Each
MakeSpace operations corresponds to a memory allocation in the later
wordLang code. By lumping together MakeSpace operations we turn
several calls to the memory allocator into a single efficient call.

[data_to_wordScript.sml](data_to_wordScript.sml):
This compiler phase removes the functional-programming-style data
abstraction of dataLang and lands in wordLang where all values are
machine words and memory is a flat finite mapping from machine
addresses to machine words. This phase introduces the garbage
collector and bignum library, among other things.

[db_varsScript.sml](db_varsScript.sml):
Defines a datatype that is handy when keeping track of which dB vars
are live when traversing a language using dB vars.

[displayLangScript.sml](displayLangScript.sml):
displayLang is a stepping stone when before pretty printing any of
the compiler's intermediate languages for inspection by humans. The
design of displayLang is intentionally very simple. The language
supports Tuples, Items (e.g. datatype constructors), and Lists.

[exportScript.sml](exportScript.sml):
Some common helper functions for writing the final byte list ->
string exporter.

[flatLangScript.sml](flatLangScript.sml):
The first intermediate language flatLang. It removes modules and
resolves all global scoping. Each value definition gets allocated a
slot in a global variable store, and each type and exception gets a
unique global identifier. It removes andalso and orelse and
replaces them with if, and removes the AallocEmpty primitive op and
replaces it with an alloc call with 0.

[flat_elimScript.sml](flat_elimScript.sml):
Implementation for flatLang dead-code elimination.

[flat_exh_matchScript.sml](flat_exh_matchScript.sml):
This compiler phase ensures that all pattern matches are exhaustive.

[flat_reorder_matchScript.sml](flat_reorder_matchScript.sml):
This compiler phase reorders patterns in pattern matches to improve
code quality.

[flat_to_patScript.sml](flat_to_patScript.sml):
This phase performs pattern-match compilation.

[flat_uncheck_ctorsScript.sml](flat_uncheck_ctorsScript.sml):
This compiler phase replaces tuples with constructors (with tag 0).

[gc](gc):
This directory contains the garbage collector (GC) algorithms and
their verification proofs.

[jsonLangScript.sml](jsonLangScript.sml):
This module contains a datatype for representing JSON objects, and
related functions. A JSON object can be an array of objects, a
string, an int, a bool or null, or it can be an object enclosed
in {}, in which case it can be viewed as a key-value store of names
(strings) and JSON objects.

[labLangScript.sml](labLangScript.sml):
The labLang intermediate language is a target-neutral assembly
language at the bottom end of the compielr backend.

[lab_filterScript.sml](lab_filterScript.sml):
This compiler phase removes all Skip instructions (generated from
Tick in stackLang).

[lab_to_targetScript.sml](lab_to_targetScript.sml):
This compiler phase generates concrete (ARM, x64, ag32, RISC-V,
MIPS) machine code from labLang assmebly programs. This phase is the
CakeML compiler's assmebler: it computes label offsets and encodes
all instructions according to the instruction encoder stored in the
compiler configuration.

[mips](mips):
This directory contains the mips-specific part of the compiler backend.

[patLangScript.sml](patLangScript.sml):
The patLang intermediate language follows immediately after
pattern-match compilation from flatLang. The patLang language
differs from earlier languages in that it uses de Bruijn indices
for variable names.

[pat_to_closScript.sml](pat_to_closScript.sml):
The translation from patLang to closLang is very simple.
Its main purpose is simplifying the semantics of some operations,
for example to explicitly raise an exception for Div so the semantics
in closLang can make more assumptions about the arguments.

[presLangScript.sml](presLangScript.sml):
Functions for converting various intermediate languages
into displayLang representations.

[proofs](proofs):
This directory contains the correctness proofs for all of the
different phases of the compiler backend.

[reg_alloc](reg_alloc):
This directory contains the implementation of the register allocator
and parallel-move algorithms.

[riscv](riscv):
This directory contains the RISC-V-specific part of the compiler backend.

[semantics](semantics):
This directory contains the definition of the semantics for each
intermediate language that is used in the compiler backend. This
directory also contains generic properties about the semantics of each
intermediate language.

[source_to_flatScript.sml](source_to_flatScript.sml):
This is the compiler phase that translates the CakeML source
language into flatLang.

[stackLangScript.sml](stackLangScript.sml):
The stackLang intermediate language is a structured programming
language with function calls, while loops, if statements, etc. All
assignments are assembly instructions and register allocation is
assumed to have been done. This is the language within which stack
operations get optimised and turned into normal memory accesses.

[stack_allocScript.sml](stack_allocScript.sml):
This compiler phase introduces the implementation of the memory
allocator and its garbage collector. It traverses the given code and
replaces all calls to Alloc by calls to code that it inserts into
the compiled program. the inserted code is a stackLang
implementation of the garbage collector.

[stack_namesScript.sml](stack_namesScript.sml):
This compiler phase renames the registers to fit with the target
architecture.

[stack_removeScript.sml](stack_removeScript.sml):
This compiler phase implements all stack operations as normal memory
load/store operations.

[stack_to_labScript.sml](stack_to_labScript.sml):
This compiler phase maps stackLang programs, which has structure
such as If, While, Return etc, to labLang programs that are a soup
of goto-like jumps.

[wordLangScript.sml](wordLangScript.sml):
The wordLang intermediate language consists of structured programs
that overate over machine words, a list-like stack and a flat memory.
This is the language where register allocation is performed.

[wordLangSyntax.sml](wordLangSyntax.sml):
ML functions for dealing with the syntax of wordLang programs.

[word_allocScript.sml](word_allocScript.sml):
This is the compiler's regsiter allocator. It supports different modes:
    0) simple allocator, no spill heuristics;
    1) simple allocator + spill heuristics;
    2) IRC allocator, no spill heuristics (default);
    3) IRC allocator + spill heuristics;
    4) linear scan register allocator.

[word_bignumScript.sml](word_bignumScript.sml):
The bignum library used by the CakeML compiler. Note that the
implementation is automatically generated from a shallow embedding
that is part of the HOL distribution in mc_multiwordTheory.

[word_elimScript.sml](word_elimScript.sml):
Implementation for wordLang dead-code elimination.

[word_instScript.sml](word_instScript.sml):
This compiler phase implements instruction selection. It uses the
Maximal Munch strategy.

[word_removeScript.sml](word_removeScript.sml):
This simple compiler phase removes `MustTerminate`, which is a
semantic-device used to help keep the logical clocks in sync in the
data_to_word correctness proofs.

[word_simpScript.sml](word_simpScript.sml):
This compiler phase performs lightweight optimisations on wordLang
programs. It is in particular designed to clean up some awkward
patterns that can be produced by the data_to_word compiler.

[word_to_stackScript.sml](word_to_stackScript.sml):
This compiler phase maps wordLang programs into stackLang
programs. The most complicated part is the handling of spilled
variables in conjunction with function calls. This compiler phase
also introduces the so called bitmaps that the garbage collector
uses to known which variables it should treat as roots in a given
stack frame.

[word_to_wordScript.sml](word_to_wordScript.sml):
This compiler phase composes the phases internal to wordLang:
    1) Inst select (with a few optimizations);
    2) SSA;
    3) Dead code elim (not written yet);
    4) 3-to-2 regs for certain configs;
    5) reg_alloc;
    6) word_to_stack.

[x64](x64):
This directory contains the x64-specific part of the compiler backend.
