signature eval_cake_icompile_x64Lib =
sig

  include Abbrev

  val init_icompile : term -> thm * thm * string

  val icompile : string -> thm -> string -> term -> thm * string

  val end_icompile : thm -> thm -> string -> term -> thm

  val print_to_file : thm -> string -> unit
end