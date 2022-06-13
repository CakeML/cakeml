open libmLib sinDeg3Theory;

val _ = new_theory "sinExample";

Theorem sin_cml_code_corr = implement sin_example_def "sin"

val _ = export_theory();
