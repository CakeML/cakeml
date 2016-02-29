signature basicComputeLib =
sig
   val add_basic_compset : computeLib.compset -> unit
   val add_datatype : computeLib.compset -> Type.hol_type -> unit
   val the_basic_compset : computeLib.compset
end
