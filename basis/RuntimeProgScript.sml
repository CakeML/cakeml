(*
  Module that contains a few special functions, e.g. a function for
  forcing a full GC to run, a function for producing debug output.
*)
open preamble ml_translatorLib ml_progLib cfDivTheory
     mloptionTheory basisFunctionsLib

val _ = new_theory "RuntimeProg";

val _ = translation_extends "cfDiv";
val cakeml = append_prog o process_topdecs;

val _ = ml_prog_update (open_module "Runtime");

Definition fullGC_def:
  fullGC (u:unit) = force_unit_type u (force_gc_to_run 0 0)
End

val () = next_ml_names := ["fullGC"];
val result = translate fullGC_def;

Definition fail_def:
  fail (u:unit) = force_unit_type u (force_out_of_memory_error u)
End

val () = next_ml_names := ["fail"];
val result = translate fail_def;

Definition debugMsg_def:
  debugMsg s = empty_ffi s
End

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

Quote cakeml:
  fun abort u = case u of () => exit 1
End

Quote cakeml:
  fun assert cond msg =
    if cond
    then ()
    else (debugMsg msg;
          abort());
End

val _ = ml_prog_update (close_module NONE);

val _ = export_theory();
