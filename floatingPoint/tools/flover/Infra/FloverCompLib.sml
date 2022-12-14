(**
  Small changes to computeLib for FloVer
**)
structure FloverCompLib =
struct
open computeLib;

val _ = computeLib.del_funs [sptreeTheory.subspt_def];

val _ = computeLib.add_funs [realTheory.REAL_INV_1OVER];
val _ = computeLib.add_funs [sptreeTheory.subspt_eq];

end
