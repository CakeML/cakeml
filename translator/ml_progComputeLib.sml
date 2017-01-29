structure ml_progComputeLib =
struct

open HolKernel boolLib bossLib

val add_env_compset = computeLib.extend_compset
  [computeLib.Defs
    [ml_progTheory.write_simp
    ,ml_progTheory.write_cons_simp
    ,ml_progTheory.write_mod_simp
    ,ml_progTheory.empty_simp
    ,ml_progTheory.merge_env_simp
    (*,ml_progTheory.SND_ALOOKUP_INTRO*)
    ,namespaceTheory.mk_id_def
    ,ml_progTheory.nsLookup_nsAppend_Short
    ]]

end
