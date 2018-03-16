open preamble ml_translatorLib ml_progLib std_preludeTheory
     mloptionTheory

val _ = new_theory"RuntimeProg"

val _ = translation_extends"std_prelude"

val () = generate_sigs := true;

val _ = concretise_all () (* TODO: better to leave more abstract longer... *)

val _ = ml_prog_update (open_module "Runtime");

val fullGC_def = Define `
  fullGC (u:unit) = force_gc_to_run 0 0`;

val () = next_ml_names := ["fullGC"];
val result = translate fullGC_def;

val debugMsg_def = Define `
  debugMsg s = empty_ffi s`;

val () = next_ml_names := ["debugMsg"];
val result = translate debugMsg_def;

val sigs = module_signatures ["fullGC", "debugMsg"];

val _ = ml_prog_update (close_module (SOME sigs));

val _ = export_theory();
