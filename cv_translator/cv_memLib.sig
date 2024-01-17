signature cv_memLib =
sig
  include Abbrev

  val cv_rep_thms     : unit -> (term * thm) list

  val cv_pre_thms     : unit -> thm list

  val cv_inline_thms  : unit -> thm list

  val cv_from_to_thms : unit -> thm list

end
