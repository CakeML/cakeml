signature cv_memLib =
sig
  include Abbrev

  val quiet           : bool ref
  val cv_print        : string -> unit
  val cv_print_thm    : thm -> unit
  val cv_time         : ('a -> 'b) -> 'a -> 'b

  val cv_rep_thms     : unit -> (term * thm) list

  val cv_pre_thms     : unit -> thm list

  val cv_inline_thms  : unit -> thm list

  val cv_from_to_thms : unit -> thm list

end
