open preamble
     ml_translatorTheory ml_translatorLib ml_progLib cfLib basisFunctionsLib
     mlstringTheory runtimeFFITheory RuntimeProgTheory

val _ = new_theory"RuntimeProof";

val _ = translation_extends "RuntimeProg";
val _ = option_monadsyntax.temp_add_option_monadsyntax();

(* heap predicate for the (trivial) runtime state *)

val RUNTIME_def = Define `
  RUNTIME =
    IOx runtime_ffi_part ()`

val RUNTIME_FFI_part_hprop = Q.store_thm("RUNTIME_FFI_part_hprop",
`FFI_part_hprop RUNTIME`,
  rw [RUNTIME_def,cfHeapsBaseTheory.IO_def,cfMainTheory.FFI_part_hprop_def,
      cfHeapsBaseTheory.IOx_def, runtime_ffi_part_def,
      set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
      set_sepTheory.cond_STAR ]
  \\ fs[set_sepTheory.one_def]);

val st = get_ml_prog_state();

val Runtime_exit_spec = Q.store_thm("Runtime_exit",
  `app (p:'ffi ffi_proj) ^(fetch_v "Runtime.exit" st) [uv]
     (RUNTIME)
     (POSTf n. λc b. RUNTIME * &(n = "exit" /\ c = [] /\ b = [])
                     * SEP_EXISTS loc. W8ARRAY loc [])`,
  xcf "Runtime.exit" st
  \\ xlet `POSTv loc. RUNTIME * W8ARRAY loc []`
  THEN1
   (simp[cf_aw8alloc_def]
    \\ irule local_elim \\ reduce_tac
    \\ simp[app_aw8alloc_def] \\ xsimpl)
  \\ xffi
  \\ simp[RUNTIME_def,runtime_ffi_part_def,IOx_def]
  \\ xsimpl
  \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
  \\ qmatch_goalsub_abbrev_tac `IO s u ns`
  \\ MAP_EVERY qexists_tac [`ns`,`u`,`s`]
  \\ unabbrev_all_tac \\ xsimpl
  \\ rw[mk_ffi_next_def,encode_def,decode_def,ffi_exit_def]
  \\ xsimpl \\ fs[SEP_IMP_def]
  \\ fs[SEP_IMP_def]
  \\ xsimpl \\ metis_tac[]);

val RUNTIME_HPROP_INJ = Q.store_thm("RUNTIME_HPROP_INJ[hprop_inj]",
  `!cl1 cl2. HPROP_INJ (RUNTIME) (RUNTIME) (T)`,
  rw[HPROP_INJ_def,STAR_def,EQ_IMP_THM]
  THEN1 (asm_exists_tac \\ rw[] \\ rw[SPLIT_emp1,cond_def])
  \\ fs[SPLIT_emp1,cond_def] \\ metis_tac[]);

val _ = export_theory();
