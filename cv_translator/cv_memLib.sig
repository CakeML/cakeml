signature cv_memLib =
sig
  include Abbrev

  datatype verbosity = Silent | Quiet | Verbose;

  val verbosity_level : verbosity ref
  val cv_print        : verbosity -> string -> unit
  val cv_print_term   : verbosity -> term -> unit
  val cv_print_thm    : verbosity -> thm -> unit
  val cv_time         : ('a -> 'b) -> 'a -> 'b

  val cv_rep_thms     : unit -> (term * thm) list
  val cv_pre_thms     : unit -> thm list
  val cv_inline_thms  : unit -> thm list
  val cv_from_to_thms : unit -> thm list

  val cv_rep_add      : thm -> unit
  val cv_pre_add      : thm -> unit
  val cv_inline_add   : thm -> unit
  val cv_from_to_add  : thm -> unit

end
