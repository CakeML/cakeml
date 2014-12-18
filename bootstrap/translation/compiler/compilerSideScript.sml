open HolKernel boolLib bossLib lcsymtacs;
open compilerMLTheory ml_translatorLib;

val _ = new_theory "compilerSide";

val _ = translation_extends"compilerML";

val inf_type_to_string_side_thm = Q.store_thm ("inf_type_to_string_side_thm",
`(!t. inf_type_to_string_side t) ∧
 (!ts. inf_types_to_string_side ts)`,
 ho_match_mp_tac infer_tTheory.infer_t_induction >>
 rw [] >>
 rw [Once inf_type_to_string_side_def, tc_to_string_side_def] >>
 fs [] >-
 fs [Once inf_type_to_string_side_def] >>
 pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once inf_type_to_string_side_def]) >>
 rw [] >>
 fs [Once inf_type_to_string_side_def]);

val compile_print_vals_side_thm = store_thm("compile_print_vals_side_thm",
  ``∀ls a b. compile_print_vals_side ls a b``,
  Induct >> simp[Once compile_print_vals_side_def,inf_type_to_string_side_thm])

val pushanyint_side_thm = store_thm("pushanyint_side_thm",
  ``∀i. pushanyint_side i``,
  ho_match_mp_tac compilerTerminationTheory.PushAnyInt_ind >>
  rw[] >> rw[Once pushanyint_side_def] >>
  rw[toBytecodeTheory.maxPushInt_def])

val compile_envref_side_thm = store_thm("compile_envref_side_thm",
  ``∀a b c. compile_envref_side a b c``,
  rw[compile_envref_side_def,pushanyint_side_thm])

val compile_varref_side_thm = store_thm("compile_varref_side_thm",
  ``∀a b c. compile_varref_side a b c``,
  rw[compile_varref_side_def,compile_envref_side_thm])

val emit_ceenv_side_thm = store_thm("emit_ceenv_side_thm",
  ``∀a b c. emit_ceenv_side a b c``,
  rw[emit_ceenv_side_def,compile_varref_side_thm])

val cons_closure_side_thm = store_thm("cons_closure_side_thm",
  ``∀a b c d e. cons_closure_side a b c d e``,
  rw[cons_closure_side_def,pushanyint_side_thm,emit_ceenv_side_thm])

val compile_closures_side_thm = store_thm("compile_closures_side_thm",
  ``∀a b c d. compile_closures_side a b c d``,
  rw[compile_closures_side_def,cons_closure_side_thm])

val prim1_to_bc_side_thm = store_thm("prim1_to_bc_side_thm",
  ``∀x. prim1_to_bc_side x``,
  rw[prim1_to_bc_side_def,pushanyint_side_thm])

val compile_side_thm = store_thm("compile_side_thm",
  ``(∀a b c d e. compile_side a b c d e) ∧
    (∀a b c d e f g. compile_bindings_side a b c d e f g) ∧
    (∀a b c d. compile_nts_side a b c d)``,
  ho_match_mp_tac compilerTerminationTheory.compile_ind >> rw[] >>
  rw[Once compile_side_def,pushanyint_side_thm,
     compile_varref_side_thm,compile_closures_side_thm,
     prim1_to_bc_side_thm])

val cce_aux_side_thm = store_thm("cce_aux_side_thm",
  ``∀x y. cce_aux_side x y``,
  rw[cce_aux_side_def,compile_side_thm])

val compile_code_env_side_thm = store_thm("compile_code_env_side_thm",
  ``∀a b. compile_code_env_side a b``,
  rw[compile_code_env_side_def,cce_aux_side_thm])

val compile_cexp_side_thm = store_thm("compile_cexp_side_thm",
  ``∀a b c d. compile_cexp_side a b c d``,
  rw[compile_cexp_side_def,compile_side_thm,compile_code_env_side_thm])

val compile_top_side_thm = store_thm("compile_top_side_thm",
  ``∀x y z. compile_top_side x y z``,
  rw[compile_top_side_def,compile_print_top_side_def,compile_cexp_side_thm] >>
  simp[compile_print_dec_side_def] >> rpt gen_tac >>
  qmatch_abbrev_tac`(a ==> b) ∧ c` >>
  qsuff_tac`b`>-rw[]>> unabbrev_all_tac >>
  simp[compile_print_vals_side_thm])

val _ = update_precondition (EQT_INTRO(SPEC_ALL compile_top_side_thm));

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory ();
