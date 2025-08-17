(**
  This file contains some type abbreviations, to ease writing.
 **)
Theory Abbrevs
Ancestors
  real sptree MachineType
Libs
  realLib preambleFloVer

(**
For the moment we need only one interval type in HOL, since we do not have the
problem of computability as we have it in Coq
**)
Type interval = “:real#real”

Definition IVlo_def:
  IVlo (iv:interval) = FST iv
End

Definition IVhi_def:
  IVhi (iv:interval) = SND iv
End

(**
Later we will argue about program preconditions.
Define a precondition to be a function mapping numbers (resp. variables) to intervals.
**)
Type precond = “:num->interval”

(**
  Abbreviation for the type of a variable environment, which should be a partial function
**)
Type env = “:num -> real option”

(**
  The empty environment must return NONE for every variable
**)
Definition emptyEnv_def:
  emptyEnv (x:num) = NONE
End

(**
  Define environment update function as abbreviation, for variable environments
**)
Definition updEnv_def:
  updEnv (x:num) (v:real) (E:env) (y:num) :real option =
    if y = x then SOME v else E y
End

Definition noDivzero_def:
  noDivzero (a:real) (b:real) = (a < &0 \/ &0 < b)
End

val _ = export_rewrites ["IVlo_def", "IVhi_def",
                         "emptyEnv_def", "updEnv_def"]

