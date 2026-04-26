Monadic definitions of stateful functions used in the basis

These functions are generated and verified using a monad type, and are then
translated to imperative CakeML code by the monadic translator.

[heap_list_sort_monadicScript.sml](heap_list_sort_monadicScript.sml):
Monadic variants of the heap-list sort functions, and proofs of equivalence.

[heap_list_sort_translationScript.sml](heap_list_sort_translationScript.sml):
Post-translation of heap_list_sort

[merge_run_sort_monadicScript.sml](merge_run_sort_monadicScript.sml):
Monadic variants of the merge-run-sort functions, and proofs of equivalence.

[merge_run_sort_translationScript.sml](merge_run_sort_translationScript.sml):
Post-translation of merge_run_sort
