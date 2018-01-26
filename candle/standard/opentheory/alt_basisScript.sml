open basis
open ml_progLib basis_ffiTheory semanticsLib helperLib set_sepTheory
     cfHeapsBaseTheory

val _ = new_theory"alt_basis";

val whole_prog_spec_extra_def = Define `
  whole_prog_spec_extra fv cl fs STORE_PROP store post <=>
    ?fs'.
    app (basis_proj1, basis_proj2) fv [Conv NONE []]
      (COMMANDLINE cl * STDIO fs * STORE_PROP store)
      (POSTv uv. &UNIT_TYPE () uv * STDIO fs') /\
      post (fs' with numchars := fs.numchars)`;

fun mk_main_call s =
  ``Tdec (Dlet unknown_loc (Pcon NONE []) (App Opapp [Var (Short ^s); Con NONE []]))``;
val fname = mk_var("fname",``:string``);
val main_call = mk_main_call fname;

val whole_prog_spec_semantics_prog = Q.store_thm("whole_prog_spec_semantics_prog",
  `∀fname fv.
     ML_code env1 (init_state (basis_ffi cl fs)) prog NONE env2 st2 ==>
     lookup_var fname env2 = SOME fv ==>
     whole_prog_spec_extra fv cl fs SP store Q ==>
     no_dup_mods (SNOC ^main_call prog) (init_state (basis_ffi cl fs)).defined_mods /\
     no_dup_top_types (SNOC ^main_call prog) (init_state (basis_ffi cl fs)).defined_types ==>
     (?h1 h2. SPLIT (st2heap (basis_proj1, basis_proj2) st2) (h1,h2) /\ (COMMANDLINE cl * STDIO fs * SP store) h1)
   ==>
   ∃io_events fs'.
     semantics_prog (init_state (basis_ffi cl fs)) env1
       (SNOC ^main_call prog) (Terminate Success io_events) /\
     extract_fs fs io_events = SOME fs' ∧ Q fs'`,
  rw[whole_prog_spec_extra_def]
  \\ drule (GEN_ALL call_main_thm2)
  \\ rpt(disch_then drule)
  \\ disch_then (qspecl_then [`h2`, `h1`] mp_tac)
  \\ impl_keep_tac
  >- (
    rw[STDIO_def]
    \\ match_mp_tac FFI_part_hprop_STAR \\ disj1_tac
    \\ ho_match_mp_tac FFI_part_hprop_SEP_EXISTS
    \\ metis_tac[IOFS_FFI_part_hprop] )
  \\ rw[]
  \\ asm_exists_tac \\ rw[]
  \\ rw[extract_fs_def,PULL_EXISTS]
  \\ drule RTC_call_FFI_rel_IMP_basis_events
  \\ simp[Once ml_progTheory.init_state_def,Once basis_ffi_def]
  \\ simp[Once ml_progTheory.init_state_def,Once basis_ffi_def]
  \\ simp[Once extract_fs_with_numchars_def]
  \\ simp[Once ml_progTheory.init_state_def]
  \\ rw[basis_proj1_write,Once basis_ffi_def]
  \\ `∃ll. SND st3.ffi.ffi_state = fs' with numchars := ll` suffices_by ( rw[] \\ rw[] )
  \\ fs[STDIO_def, IOFS_def,cfHeapsBaseTheory.IO_def,
        cfHeapsBaseTheory.IOx_def, set_sepTheory.SEP_CLAUSES,
        set_sepTheory.SEP_EXISTS_THM, fsFFITheory.fs_ffi_part_def]
  \\ fs[GSYM set_sepTheory.STAR_ASSOC]
  \\ fs[Once STAR_def]
  \\ fs[set_sepTheory.one_STAR]
  \\ qmatch_assum_abbrev_tac`one ffip _`
  \\ fs[one_def]
  \\ `ffip ∈ (st2heap (basis_proj1,basis_proj2) st3)` by cfHeapsBaseLib.SPLIT_TAC
  \\ fs [cfStoreTheory.st2heap_def, cfStoreTheory.FFI_part_NOT_IN_store2heap,
         Abbr`ffip`,cfStoreTheory.ffi2heap_def]
  \\ Cases_on `parts_ok st3.ffi (basis_proj1, basis_proj2)`
  \\ fs[FLOOKUP_DEF, MAP_MAP_o, n2w_ORD_CHR_w2n, basis_proj1_write]
  \\ FIRST_X_ASSUM(ASSUME_TAC o Q.SPEC`"write"`)
  \\ fs[basis_proj1_write,STAR_def,cond_def]
  \\ metis_tac[]
  );

val _ = export_theory();
