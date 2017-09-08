open preamble ml_translatorTheory ml_translatorLib ml_progLib
     basisFunctionsLib fsFFIProofTheory optionMonadTheory cfHeapsBaseTheory
     ltemporalTheory mlcommandLineProgTheory fsFFITheory set_sepTheory
     cfMainTheory fsioProgConstantsTheory cfLetAutoTheory cfLetAutoLib
     cfHeapsBaseLib

val _ = new_theory"fsioProof";

(*---------------------------------------------------------------------------*)
(* GENERALISED FFI *)

val basis_ffi_oracle_def = Define `
  basis_ffi_oracle =
    \name (cls,fs) bytes.
     if name = "write" then
       case ffi_write bytes fs of
       | SOME (bytes,fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     if name = "read" then
       case ffi_read bytes fs of
       | SOME (bytes,fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     if name = "getArgs" then
       case ffi_getArgs bytes cls of
       | SOME (bytes,cls) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     if name = "open_in" then
       case ffi_open_in bytes fs of
       | SOME (bytes,fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     if name = "open_out" then
       case ffi_open_out bytes fs of
       | SOME (bytes,fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     if name = "close" then
       case ffi_close bytes fs of
       | SOME (bytes,fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     Oracle_fail`

val basis_fs_def = Define`
  basis_fs inp files numchars = 
    <| files := ((strlit "stdin",inp)::(strlit "stdout","")::(strlit "stderr","")::files);
       infds := [(0,strlit "stdin",0);(1,strlit "stdout",0);(2,strlit "stderr",0)];
       numchars := numchars |> : IO_fs`

(* standard streams are initialized *)
val basis_ffi_def = Define `
  basis_ffi (inp: string) (cls: string list) files numchars =
    <| oracle := basis_ffi_oracle
     ; ffi_state := (cls, basis_fs inp files numchars)
     ; final_event := NONE
     ; io_events := [] |>`;

val basis_proj1_def = Define `
  basis_proj1 = (\(cls, fs).
    FEMPTY |++ ((mk_proj1 commandLine_ffi_part cls) ++ (mk_proj1 fs_ffi_part fs)))`;

val basis_proj2_def = Define `
  basis_proj2 =
    [mk_proj2 commandLine_ffi_part;
     mk_proj2 fs_ffi_part]`;

val basis_proj1_write = Q.store_thm("basis_proj1_write",
  `basis_proj1 ffi ' "write" = encode(SND ffi)`,
  PairCases_on`ffi` \\ EVAL_TAC);

(* builds the file system from a list of events *)
val extract_fs_def = Define `
  (extract_fs init_fs [] = SOME init_fs) ∧ 
  (extract_fs init_fs ((IO_event name bytes)::xs) =
  (* monadic style doesn't work here *)
    case (ALOOKUP [("open_in",ffi_open_in); ("write",ffi_write);
                           ("open_out",ffi_open_out); ("read",ffi_read);
                           ("close",ffi_close);
                           ("getArgs", (λ b fs. SOME (b,fs)))] name) of
    | SOME ffi_fun => (case ffi_fun (MAP FST bytes) init_fs of
                       | SOME (bytes',fs') => extract_fs fs' xs
                       | NONE => NONE)
    | NONE => NONE)`

val extract_fs_APPEND = Q.store_thm("extract_fs_APPEND",
 `!xs ys init_fs. extract_fs init_fs (xs ++ ys) = 
   case extract_fs init_fs xs of
      | NONE => NONE
      | SOME fs => extract_fs fs ys`,
  induct_on`xs` >> rw[extract_fs_def] >> CASE_TAC >>(
  cases_on`h` >> fs[extract_fs_def] >>
  cases_on`s = "open_in"` >> fs[] >- rpt(CASE_TAC >> fs[]) >>
  cases_on`s = "write"` >> fs[] >- rpt(CASE_TAC >> fs[]) >>
  cases_on`s = "open_out"` >> fs[] >- rpt(CASE_TAC >> fs[]) >>
  cases_on`s = "read"` >> fs[] >- rpt(CASE_TAC >> fs[]) >>
  cases_on`s = "close"` >> fs[] >- rpt(CASE_TAC >> fs[]) >>
  cases_on`s = "getArgs"` >> fs[]));

(*-------------------------------------------------------------------------------------------------*)

(*These theorems are need to be remade to use cfMain for projs, oracle or ffi that aren't basis_ffi*)

(* TODO: move *)

(* the failure of an fs ffi call doesn't depend on the filesystem *)
val fs_ffi_NONE_irrel = Q.store_thm("fs_ffi_NONE_irrel",
 `!f. f ∈ {ffi_read; ffi_write; ffi_open_in; ffi_open_out; ffi_close} ∧
      f bytes fs = NONE ⇒ f bytes fs' = NONE`,
  rw[] >>
  fs[ffi_read_def,ffi_write_def,ffi_open_in_def,ffi_open_out_def,ffi_close_def] >>
  every_case_tac >> fs[OPTION_CHOICE_EQ_NONE]);

(*RTC_call_FFI_rel_IMP_basis_events show that extracting output from two ffi_states will use the
  same function if the two states are related by a series of FFI_calls. If this is the case for
  your oracle (and projs), then this proof should be relatively similar. Note
  that to make the subsequent proofs similar one should show an equivalence between
  extract_output and proj1  *)
val RTC_call_FFI_rel_IMP_basis_events = Q.store_thm ("RTC_call_FFI_rel_IMP_basis_events",
  `!inp fs ll st st'. call_FFI_rel^* st st' ==> st.oracle = basis_ffi_oracle ==>
  (extract_fs (basis_fs inp fs ll) st.io_events  
     = fsFFI$decode (basis_proj1 st.ffi_state ' "write") ==>
   extract_fs (basis_fs inp fs ll) st'.io_events 
     = fsFFI$decode (basis_proj1 st'.ffi_state ' "write"))`, 
     NTAC 3 strip_tac
  \\ HO_MATCH_MP_TAC RTC_INDUCT \\ rw [] \\ fs [fsFFITheory.decode_def]
  \\ fs [evaluatePropsTheory.call_FFI_rel_def]
  \\ fs [ffiTheory.call_FFI_def]
  \\ Cases_on `st.final_event = NONE` \\ fs [] \\ rw []
  \\ FULL_CASE_TAC \\ fs [] \\ rw [] \\ fs []
  \\ FULL_CASE_TAC \\ fs [] \\ rw [] \\ fs []
  \\ Cases_on `f` \\ fs []
  \\ fs [extract_fs_APPEND,extract_fs_def,basis_proj1_write] \\ rfs []
  \\ first_x_assum match_mp_tac
  \\ qpat_x_assum`_ = Oracle_return _ _`mp_tac
  \\ simp[basis_ffi_oracle_def]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ rpt(full_case_tac \\ fs[option_eq_some,MAP_ZIP] \\ rw[]) >>
  rfs[MAP_ZIP]);

(* the first condition for the previous theorem holds for the
  init_state ffi  *)
val extract_fs_basis_ffi = Q.store_thm ("extract_fs_basis_ffi",
  `extract_fs (basis_fs inp fs ll) (basis_ffi inp cls fs ll).io_events =
   decode (basis_proj1 (basis_ffi inp cls fs ll).ffi_state ' "write")`,
  rw[ml_progTheory.init_state_def,extract_fs_def,basis_ffi_def,basis_proj1_write]);


val emp_precond = Q.store_thm("emp_precond",
  `emp {}`, EVAL_TAC);

val append_hprop = Q.store_thm ("append_hprop",
  `A s1 /\ B s2 ==> DISJOINT s1 s2 ==> (A * B) (s1 ∪ s2)`,
  rw[set_sepTheory.STAR_def] \\ SPLIT_TAC
);

(* TODO: avoid using constant for iobuff_loc *)

val IOFS_precond = Q.store_thm("IOFS_precond",
  `!fs. wfFS fs ⇒ liveFS fs ⇒ LENGTH v = 258 ⇒
   IOFS fs
    ({FFI_part (encode fs) (mk_ffi_next fs_ffi_part) (MAP FST (SND(SND fs_ffi_part))) events}
    ∪ {Mem 1 (W8array v)})`,
  rw[IOFS_def,cfHeapsBaseTheory.IOx_def,fs_ffi_part_def,cfHeapsBaseTheory.IO_def,one_def,
     IOFS_iobuff_def,W8ARRAY_def,cell_def]
  \\ rw[set_sepTheory.SEP_EXISTS_THM,set_sepTheory.cond_STAR,set_sepTheory.SEP_CLAUSES]
  \\ qexists_tac`events` \\  qexists_tac`v` \\ qexists_tac`1`
  \\ fs[SEP_CLAUSES,one_STAR,one_def,append_hprop]
  );

val STDIO_precond = Q.store_thm("STDIO_precond",
` ALOOKUP fs.infds 0 = SOME (strlit "stdin",inp) ==>
  ALOOKUP fs.infds 1 = SOME (strlit "stdout",STRLEN out) ==>
  ALOOKUP fs.infds 2 = SOME (strlit "stderr",STRLEN err) ==>
  ALOOKUP fs.files (strlit "stdout") = SOME out ==>
  ALOOKUP fs.files (strlit "stderr") = SOME err ==>
  wfFS fs ==> liveFS fs ==> LENGTH v = 258 ==>     
  STDIO fs
    ({FFI_part (encode (fs with numchars := (THE (LDROP k fs.numchars)))) 
               (mk_ffi_next fs_ffi_part) (MAP FST (SND(SND fs_ffi_part))) events}
     ∪ {Mem 1 (W8array v)})`,
  rw[STDIO_def,IOFS_precond,SEP_EXISTS_THM,SEP_CLAUSES] >>
  qexists_tac`k` >>
  `(fs with numchars := THE (LDROP k fs.numchars)) = 
   fsupdate fs 1 k (STRLEN out) out`
    by fs[fsupdate_def,ALIST_FUPDKEY_unchanged,IO_fs_component_equality] >>
  mp_tac (Q.SPEC `fsupdate fs 1 k (STRLEN out) out` IOFS_precond) >>
  impl_tac >-(
    `MEM 1 (MAP FST fs.infds)` by
      (fs[MEM_MAP] >> qexists_tac`(1,strlit "stdout",STRLEN out)` >> 
      imp_res_tac ALOOKUP_MEM >> fs[]) >>
    fs[wfFS_fsupdate]) >>
  impl_tac >- fs[liveFS_fsupdate] >>
  fs[]);

(*call_main_thm_basis uses call_main_thm2 to get Semantics_prog, and then uses the previous two
  theorems to prove the outcome of extract_output. If RTC_call_FFI_rel_IMP* uses proj1, after
  showing that post-condition which gives effects your programs output is an FFI_part and
  assuming that parts_ok is satisfied, an assumption about proj1 and the ffi_state should be
  derived which should fit the function on some st.ffi_state which returns extract_output on
  st.io_events  *)

fun mk_main_call s =
  ``Tdec (Dlet unknown_loc (Pcon NONE []) (App Opapp [Var (Short ^s); Con NONE []]))``;
val fname = mk_var("fname",``:string``);
val main_call = mk_main_call fname;

val call_main_thm_basis = Q.store_thm("call_main_thm_basis",
`!fname fv.
 ML_code env1 (init_state (basis_ffi inp cls fs ll)) prog NONE env2 st2 ==>
   lookup_var fname env2 = SOME fv ==>
  app (basis_proj1, basis_proj2) fv [Conv NONE []] P
    (POSTv uv. &UNIT_TYPE () uv * (SEP_EXISTS k. 
        IOFS (fs0 with numchars := THE (LDROP k fs0.numchars)) * &R fs0) * Q) ==>
  no_dup_mods (SNOC ^main_call prog) (init_state (basis_ffi inp cls fs ll)).defined_mods /\
  no_dup_top_types (SNOC ^main_call prog) (init_state (basis_ffi inp cls fs ll)).defined_types ==>
  (?h1 h2. SPLIT (st2heap (basis_proj1, basis_proj2) st2) (h1,h2) /\ P h1)
  ==>
    ∃io_events k. R fs0 /\
    semantics_prog (init_state (basis_ffi inp cls fs ll)) env1
      (SNOC ^main_call prog) (Terminate Success io_events) /\
    extract_fs (basis_fs inp fs ll) io_events = 
        SOME (fs0 with numchars := THE (LDROP k fs0.numchars))`,
    rw[]
    \\ `app (basis_proj1,basis_proj2) fv [Conv NONE []] P (POSTv uv. &UNIT_TYPE () uv *
         ((SEP_EXISTS k.IOFS (fs0 with numchars := THE (LDROP k fs0.numchars)) * &R fs0  ) * Q))` 
          by (fs[STAR_ASSOC])
    \\ drule (GEN_ALL call_main_thm2)
    \\ rpt(disch_then drule)
    \\ qmatch_goalsub_abbrev_tac`FFI_part_hprop X`
    \\ `FFI_part_hprop X`
    by(simp[Abbr`X`]
       \\ match_mp_tac FFI_part_hprop_STAR \\ disj1_tac
       \\ ho_match_mp_tac FFI_part_hprop_SEP_EXISTS \\ rw[]
       \\ metis_tac[IOFS_FFI_part_hprop, FFI_part_hprop_STAR])
    \\ disch_then (qspecl_then [`h2`, `h1`] mp_tac) \\ rw[Abbr`X`]
    \\ fs[SEP_EXISTS_THM,SEP_CLAUSES]
    \\ `R fs0` by metis_tac[cond_STAR,STAR_ASSOC,STAR_COMM]
    \\ map_every qexists_tac [`st3.ffi.io_events`,`k`]
    \\ fs[]
    \\ `decode (basis_proj1 st3.ffi.ffi_state ' "write") = 
            SOME (fs0 with numchars := THE (LDROP k fs0.numchars))`
        suffices_by
      (imp_res_tac RTC_call_FFI_rel_IMP_basis_events
       \\ rfs[GSYM extract_fs_basis_ffi,ml_progTheory.init_state_def,basis_ffi_def]
       \\ ASSUME_TAC extract_fs_basis_ffi \\ fs[basis_ffi_def])
    \\ fs[FFI_part_hprop_def]
    \\ fs[basis_proj1_write, IOFS_def,cfHeapsBaseTheory.IO_def,
          cfHeapsBaseTheory.IOx_def, set_sepTheory.SEP_CLAUSES,
          set_sepTheory.SEP_EXISTS_THM, fsFFITheory.fs_ffi_part_def]
    \\ fs[GSYM set_sepTheory.STAR_ASSOC] 
    \\ fs[Once STAR_def]
    \\ fs[set_sepTheory.one_STAR]
    \\ qmatch_assum_abbrev_tac`one ffip u`
    \\ fs[Once set_sepTheory.STAR_ASSOC]
    \\ NTAC 3 (fs[Once set_sepTheory.STAR_def])
    \\ fs [set_sepTheory.one_STAR,one_def]
    \\ `ffip ∈ (st2heap (basis_proj1,basis_proj2) st3)` by cfHeapsBaseLib.SPLIT_TAC
    \\ fs [cfStoreTheory.st2heap_def, cfStoreTheory.FFI_part_NOT_IN_store2heap,
           Abbr`ffip`,cfStoreTheory.ffi2heap_def]
    \\ Cases_on `parts_ok st3.ffi (basis_proj1, basis_proj2)`
    \\ fs[FLOOKUP_DEF, MAP_MAP_o, n2w_ORD_CHR_w2n, basis_proj1_write]
    \\ FIRST_X_ASSUM(ASSUME_TAC o Q.SPEC`"write"`)
    \\ fs[basis_proj1_write,STAR_def,cond_def]
    );

val basis_ffi_length_thms = save_thm("basis_ffi_length_thms", LIST_CONJ
[ffi_write_length,ffi_read_length,ffi_open_in_length,ffi_open_out_length,
 ffi_close_length, commandLineFFITheory.ffi_getArgs_length ]);

val basis_ffi_part_defs = save_thm("basis_ffi_part_defs", LIST_CONJ
[fs_ffi_part_def,commandLineFFITheory.commandLine_ffi_part_def]);

(* This is used to show to show one of the parts of parts_ok for the state after a spec *)
val oracle_parts = Q.store_thm("oracle_parts",
  `!st. st.ffi.oracle = basis_ffi_oracle /\ MEM (ns, u) basis_proj2 /\ MEM m ns /\ u m bytes (basis_proj1 x ' m) = SOME (new_bytes, w)
    ==> (?y. st.ffi.oracle m x bytes = Oracle_return y new_bytes /\ basis_proj1 x |++ MAP (\n. (n,w)) ns = basis_proj1 y)`,
  simp[basis_proj2_def,basis_proj1_def]
  \\ pairarg_tac \\ fs[]
  \\ rw[cfHeapsBaseTheory.mk_proj1_def,
        cfHeapsBaseTheory.mk_proj2_def,
        basis_ffi_oracle_def,basis_ffi_part_defs]
  \\ rw[] \\ fs[FUPDATE_LIST_THM,FAPPLY_FUPDATE_THM]
  \\ TRY (
     CASE_TAC \\ fs[cfHeapsBaseTheory.mk_ffi_next_def]
  \\ CASE_TAC \\ fs[fmap_eq_flookup,FLOOKUP_UPDATE]
  \\ rw[] )
  \\ disj2_tac
  \\ CCONTR_TAC \\ fs[] \\ rfs[]
);

(*This is an example of how to show parts_ok for a given state -- could be automate and put in ioProgLib.sml *)

val _ = export_theory();

