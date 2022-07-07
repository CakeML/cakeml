This directory contains the correctness proofs for all of the
different phases of the compiler backend.

[backendProofScript.sml](backendProofScript.sml):
Composes the correctness theorems for all of the compiler phases.

[backend_itreeProofScript.sml](backend_itreeProofScript.sml):
Compiler correctness for the itree CakeML semantics

[bvi_letProofScript.sml](bvi_letProofScript.sml):
Correctness proof for bvi_let

[bvi_tailrecProofScript.sml](bvi_tailrecProofScript.sml):
Correctness proof for bvi_tailrec

[bvi_to_dataProofScript.sml](bvi_to_dataProofScript.sml):
Correctness proof for bvi_to_data

[bvl_constProofScript.sml](bvl_constProofScript.sml):
Correctness proof for bvl_const

[bvl_handleProofScript.sml](bvl_handleProofScript.sml):
Correctness proof for bvl_handle

[bvl_inlineProofScript.sml](bvl_inlineProofScript.sml):
Correctness proof for bvi_inline

[bvl_jumpProofScript.sml](bvl_jumpProofScript.sml):
Correctness proof for bvl_jump

[bvl_to_bviProofScript.sml](bvl_to_bviProofScript.sml):
Correctness proof for bvl_to_bvi

[clos_annotateProofScript.sml](clos_annotateProofScript.sml):
Correctness proof for clos_annotate

[clos_callProofScript.sml](clos_callProofScript.sml):
Correctness proof for clos_call

[clos_constantProofScript.sml](clos_constantProofScript.sml):
Some functions that flatten a closLang/BVL/BVI/dataLang const tree
into a sequence of operations that share common data.

[clos_fvsProofScript.sml](clos_fvsProofScript.sml):
Correctness proof for clos_fvs

[clos_knownProofScript.sml](clos_knownProofScript.sml):
Correctness proof for clos_known

[clos_knownPropsScript.sml](clos_knownPropsScript.sml):
Lemmas used in proof of clos_known

[clos_letopProofScript.sml](clos_letopProofScript.sml):
Correctness proof for clos_letop

[clos_mtiProofScript.sml](clos_mtiProofScript.sml):
Correctness proof for the clos_mti compiler pass. The theorem is
proved using a backwards simulation, i.e. against the direction of
compilation.

[clos_numberProofScript.sml](clos_numberProofScript.sml):
Correctness proof for clos_number

[clos_opProofScript.sml](clos_opProofScript.sml):
Correctness proof for clos_op

[clos_ticksProofScript.sml](clos_ticksProofScript.sml):
Correctness proof for clos_ticks

[clos_to_bvlProofScript.sml](clos_to_bvlProofScript.sml):
Correctness proof for clos_to_bvl

[data_liveProofScript.sml](data_liveProofScript.sml):
Correctness proof for data_live

[data_simpProofScript.sml](data_simpProofScript.sml):
Correctness proof for data_simp

[data_spaceProofScript.sml](data_spaceProofScript.sml):
Correctness proof for data_space

[data_to_wordProofScript.sml](data_to_wordProofScript.sml):
Correctness proof for data_to_word

[data_to_word_assignProofScript.sml](data_to_word_assignProofScript.sml):
Part of the correctness proof for data_to_word

[data_to_word_bignumProofScript.sml](data_to_word_bignumProofScript.sml):
Part of the correctness proof for data_to_word

[data_to_word_gcProofScript.sml](data_to_word_gcProofScript.sml):
Part of the correctness proof for data_to_word

[data_to_word_memoryProofScript.sml](data_to_word_memoryProofScript.sml):
Part of the correctness proof for data_to_word

[experimentalLib.sml](experimentalLib.sml):
Some proof tools, mostly quite experimental, used in some of
the proofs in this directory

[flat_elimProofScript.sml](flat_elimProofScript.sml):
Correctness proof for flatLang dead code elimination

[flat_patternProofScript.sml](flat_patternProofScript.sml):
Correctness proof for flat_pattern

[flat_to_closProofScript.sml](flat_to_closProofScript.sml):
Correctness proof for flat_to_clos

[lab_filterProofScript.sml](lab_filterProofScript.sml):
Correctness proof for lab_filter

[lab_to_targetProofScript.sml](lab_to_targetProofScript.sml):
Correctness proof for lab_to_target

[source_evalProofScript.sml](source_evalProofScript.sml):
Proofs that the eval mode of the source semantics can
be switched to one that includes an oracle.

[source_letProofScript.sml](source_letProofScript.sml):
Correctness for the source_let pass.

[source_to_flatProofScript.sml](source_to_flatProofScript.sml):
Correctness proof for source_to_flat

[source_to_sourceProofScript.sml](source_to_sourceProofScript.sml):
Proof of correctness for source_to_source.

[stack_allocProofScript.sml](stack_allocProofScript.sml):
Correctness proof for stack_alloc

[stack_namesProofScript.sml](stack_namesProofScript.sml):
Correctness proof for stack_names

[stack_rawcallProofScript.sml](stack_rawcallProofScript.sml):
Correctness proof for stack_rawcall

[stack_removeProofScript.sml](stack_removeProofScript.sml):
Correctness proof for stack_remove

[stack_to_labProofScript.sml](stack_to_labProofScript.sml):
Correctness proof for stack_to_lab

[word_allocProofScript.sml](word_allocProofScript.sml):
Correctness proof for word_alloc

[word_bignumProofScript.sml](word_bignumProofScript.sml):
Correctness proof for word_bignum

[word_depthProofScript.sml](word_depthProofScript.sml):
Proves correctness of the max_depth applied to the call graph of a
wordLang program as produced by the word_depth$call_graph function.

[word_elimProofScript.sml](word_elimProofScript.sml):
Correctness proof for word_elim

[word_gcFunctionsScript.sml](word_gcFunctionsScript.sml):
Shallow embedding of garbage collector implementation

[word_instProofScript.sml](word_instProofScript.sml):
Correctness proof for word_inst

[word_removeProofScript.sml](word_removeProofScript.sml):
Correctness proof for word_remove

[word_simpProofScript.sml](word_simpProofScript.sml):
Correctness proof for word_simp

[word_to_stackProofScript.sml](word_to_stackProofScript.sml):
Correctness proof for word_to_stack

[word_to_wordProofScript.sml](word_to_wordProofScript.sml):
Correctness proof for word_to_word
