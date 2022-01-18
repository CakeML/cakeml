(*
  Evaluate some lookups in the REPL types and env
*)
open preamble repl_moduleProgTheory repl_init_typesTheory

val _ = new_theory "repl_init_props"

val env = Decls_repl_prog |> concl |> rator |> rand

Definition repl_prog_env_def:
  repl_prog_env = merge_env ^env init_env
End

Theorem isEOF_lookup = LIST_CONJ
 [EVAL “nsLookup repl_prog_types.inf_v (Long "REPL" (Short "isEOF"))”
  |> REWRITE_RULE [GSYM (EVAL “Tbool_num”),GSYM (EVAL “Tref_num”)],
  (SIMP_CONV std_ss [repl_prog_env_def] THENC ml_progLib.nsLookup_conv)
     “nsLookup repl_prog_env.v (Long "REPL" (Short "isEOF"))”,
  isEOF_def |> CONJUNCT2 |> SIMP_RULE std_ss [LENGTH,LENGTH_APPEND]]

Theorem nextString_props = LIST_CONJ
 [EVAL “nsLookup repl_prog_types.inf_v (Long "REPL" (Short "nextString"))”
  |> REWRITE_RULE [GSYM (EVAL “Tstring_num”),GSYM (EVAL “Tref_num”)],
  (SIMP_CONV std_ss [repl_prog_env_def] THENC ml_progLib.nsLookup_conv)
     “nsLookup repl_prog_env.v (Long "REPL" (Short "nextString"))”,
  nextString_def |> CONJUNCT2 |> SIMP_RULE std_ss [LENGTH,LENGTH_APPEND]]

val _ = export_theory ();
