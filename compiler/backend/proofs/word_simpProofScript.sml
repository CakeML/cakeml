open preamble wordLangTheory wordSemTheory wordPropsTheory word_simpTheory;

val _ = new_theory "word_simpProof";

val compile_exp_thm = store_thm("compile_exp_thm",
  ``wordSem$evaluate (prog,s) = (res,s2) /\ res <> SOME Error ==>
    evaluate (word_simp$compile_exp prog,s) = (res,s2)``,
  fs [word_simpTheory.compile_exp_def]);

val extract_labels_compile_exp = store_thm("extract_labels_compile_exp[simp]",
  ``!p. extract_labels (compile_exp p) = extract_labels p``,
  fs [word_simpTheory.compile_exp_def]);

val _ = export_theory();
