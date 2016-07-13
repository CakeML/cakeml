open preamble wordLangTheory

val _ = new_theory "word_simp";

val compile_exp_def = Define `
  compile_exp (e:'a wordLang$prog) = e`;

val _ = export_theory();
