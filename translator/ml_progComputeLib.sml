(*
  compset for the definitions in ml_progTheory.
*)
structure ml_progComputeLib =
struct

open HolKernel boolLib bossLib

val add_env_compset = computeLib.extend_compset
  [computeLib.Defs
    [ml_progTheory.write_simp
    ,ml_progTheory.write_cons_simp
    ,ml_progTheory.write_mod_simp
    ,ml_progTheory.empty_simp
    ,ml_progTheory.nsLookup_merge_env
    (*,ml_progTheory.SND_ALOOKUP_INTRO*)
    ,namespaceTheory.mk_id_def
    ,namespaceTheory.id_to_n_def
    ,ml_progTheory.nsLookup_nsAppend_Short
    ]]

end
