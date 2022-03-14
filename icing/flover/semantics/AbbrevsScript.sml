(**
  This file contains some type abbreviations, to ease writing.
 **)
open realTheory realLib sptreeTheory
open MachineTypeTheory
open preambleFloVer

val _ = new_theory "Abbrevs";
(**
For the moment we need only one interval type in HOL, since we do not have the
problem of computability as we have it in Coq
**)
val _ = type_abbrev("interval", ``:real#real``);
val IVlo_def = Define `IVlo (iv:interval) = FST iv`;
val IVhi_def = Define `IVhi (iv:interval) = SND iv`;

(**
Later we will argue about program preconditions.
Define a precondition to be a function mapping numbers (resp. variables) to intervals.
**)
val _ = type_abbrev ("precond", ``:num->interval``);

(**
  Abbreviation for the type of a variable environment, which should be a partial function
**)
val _ = type_abbrev("env",``:num->real option``);

(**
  The empty environment must return NONE for every variable
**)
val emptyEnv_def = Define `
  emptyEnv (x:num) = NONE`;

(**
  Define environment update function as abbreviation, for variable environments
**)
val updEnv_def = Define `
  updEnv (x:num) (v:real) (E:env) (y:num) :real option =
    if y = x then SOME v else E y`;

val noDivzero_def = Define `noDivzero (a:real) (b:real) = (a < &0 \/ &0 < b)`;

val _ = export_rewrites ["IVlo_def", "IVhi_def",
                         "emptyEnv_def", "updEnv_def"]

val _ = export_theory();
