(*
  Module that contains a few special functions, e.g. a function for
  forcing a full GC to run, a function for producing debug output.
*)
open preamble ml_translatorLib ml_progLib std_preludeTheory
     mloptionTheory basisFunctionsLib

val _ = new_theory"RuntimeProg"

val _ = translation_extends "cfDiv"

val () = generate_sigs := true;

val _ = ml_prog_update (open_module "Runtime");

val fullGC_def = Define `
  fullGC (u:unit) = force_gc_to_run 0 0`;

val () = next_ml_names := ["fullGC"];
val result = translate fullGC_def;

val debugMsg_def = Define `
  debugMsg s = empty_ffi s`;

val () = next_ml_names := ["debugMsg"];
val result = translate debugMsg_def;

val exit =
 ``[Dletrec (unknown_loc)
     ["exit","i",
      Let (SOME "y") (App (WordFromInt W8) [Var (Short "i")])
        (Let (SOME "x") (App Aw8alloc [Lit(IntLit 1);
                                       Var (Short "y")])
             (App (FFI "exit") [Lit(StrLit ""); Var (Short "x")]))]]``

val _ = append_prog exit

val abort = process_topdecs `fun abort u = exit 1`

val _ = append_prog abort

val sigs = module_signatures ["fullGC", "debugMsg","exit","abort"];

val _ = ml_prog_update (close_module (SOME sigs));

val _ = export_theory();
