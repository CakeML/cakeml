signature presLangLib =
sig

   include Abbrev

   val flat_to_strs : term (* prog *) -> string list
   val clos_to_strs : term (* prog *) -> string list
   val bvl_to_strs : term (* names *) -> term (* prog *) -> string list
   val bvi_to_strs : term (* names *) -> term (* prog *) -> string list
   val data_to_strs : term (* names *) -> term (* prog *) -> string list

   val print_strs : string list -> unit

   val write_strs_to_file : string -> string list -> unit

end
