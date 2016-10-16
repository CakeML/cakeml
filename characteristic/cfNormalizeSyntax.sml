structure cfNormalizeSyntax :> cfNormalizeSyntax = struct
open Abbrev

local
  open HolKernel boolLib bossLib cfAppTheory

  val s1 = HolKernel.syntax_fns1 "cfNormalize"
  val s2 = HolKernel.syntax_fns2 "cfNormalize"
in

val (full_normalise_tm, mk_full_normalise, dest_full_normalise, is_full_normalise) = s2 "full_normalise"
val (full_normalise_prog_tm, mk_full_normalise_prog, dest_full_normalise_prog, is_full_normalise_prog) = s1 "full_normalise_prog"
val (full_normalise_decl_tm, mk_full_normalise_decl, dest_full_normalise_decl, is_full_normalise_decl) = s1 "full_normalise_decl"

end

end
