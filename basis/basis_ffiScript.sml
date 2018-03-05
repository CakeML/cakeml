open preamble ml_translatorTheory ml_translatorLib ml_progLib
     cfLib basisFunctionsLib set_sepTheory
     fsFFITheory fsFFIPropsTheory
     CommandLineProofTheory TextIOProofTheory

val _ = new_theory"basis_ffi";

(*---------------------------------------------------------------------------*)
(* GENERALISED FFI *)

val basis_ffi_oracle_def = Define `
  basis_ffi_oracle =
    \name (cls,fs) conf bytes.
     if name = "write" then
       case ffi_write conf bytes fs of
       | SOME (bytes,fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     if name = "read" then
       case ffi_read conf bytes fs of
       | SOME (bytes,fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     if name = "get_arg_count" then
       case ffi_get_arg_count conf bytes cls of
       | SOME (bytes,cls) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     if name = "get_arg_length" then
       case ffi_get_arg_length conf bytes cls of
       | SOME (bytes,cls) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     if name = "get_arg" then
       case ffi_get_arg conf bytes cls of
       | SOME (bytes,cls) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     if name = "open_in" then
       case ffi_open_in conf bytes fs of
       | SOME (bytes,fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     if name = "open_out" then
       case ffi_open_out conf bytes fs of
       | SOME (bytes,fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     if name = "close" then
       case ffi_close conf bytes fs of
       | SOME (bytes,fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     Oracle_fail`

(* standard streams are initialized *)
val basis_ffi_def = Define `
  basis_ffi cl fs =
    <| oracle := basis_ffi_oracle
     ; ffi_state := (cl, fs)
     ; final_event := NONE
     ; io_events := [] |>`;

val basis_proj1_def = Define `
  basis_proj1 = (\(cls, fs).
    FEMPTY |++ ((mk_proj1 cl_ffi_part cls)
			++ (mk_proj1 fs_ffi_part fs)))`;

val basis_proj2_def = Define `
  basis_proj2 =
    [mk_proj2 cl_ffi_part;
     mk_proj2 fs_ffi_part]`;

val basis_proj1_write = Q.store_thm("basis_proj1_write",
  `basis_proj1 ffi ' "write" = encode(SND ffi)`,
  PairCases_on`ffi` \\ EVAL_TAC);

(* builds the file system from a list of events *)

val extract_fs_with_numchars_def = Define `
  (extract_fs_with_numchars init_fs [] = SOME init_fs) ∧
  (extract_fs_with_numchars init_fs ((IO_event name conf bytes)::xs) =
    case (ALOOKUP (SND(SND fs_ffi_part)) name) of
    | SOME ffi_fun => (case ffi_fun conf (MAP FST bytes) init_fs of
                       | SOME (bytes',fs') =>
                         if bytes' = MAP SND bytes then
                           extract_fs_with_numchars fs' xs
                         else NONE
                       | NONE => NONE)
    | NONE => extract_fs_with_numchars init_fs xs)`

val extract_fs_with_numchars_APPEND = Q.store_thm("extract_fs_with_numchars_APPEND",
  `!xs ys init_fs. extract_fs_with_numchars init_fs (xs ++ ys) =
    case extract_fs_with_numchars init_fs xs of
    | NONE => NONE
    | SOME fs => extract_fs_with_numchars fs ys`,
  Induct_on`xs` \\ simp[extract_fs_with_numchars_def]
  \\ Cases \\ simp[extract_fs_with_numchars_def]
  \\ CASE_TAC
  \\ rpt gen_tac
  \\ rpt CASE_TAC);

val extract_fs_def = Define`
  extract_fs init_fs events =
    OPTION_MAP (numchars_fupd (K init_fs.numchars))
    (extract_fs_with_numchars init_fs events)`;

(*
val extract_stdo_def = Define`
  (extract_stdo fd [] = "") ∧
  (extract_stdo fd (IO_event name conf bytes::xs) =
   if name = "write" ∧
      3 ≤ LENGTH bytes ∧
      FST(HD bytes) = fd ∧
      SND(HD bytes) = 0w
   then
     MAP (CHR o w2n o FST) (TAKE (w2n(SND(HD(TL bytes)))) (DROP 3 bytes))
     ++ extract_stdo fd xs
   else extract_stdo fd xs)`
val _ = overload_on("extract_stdout",``extract_stdo stdOut``);
val _ = overload_on("extract_stderr",``extract_stdo stdErr``);

val extract_stdo_extract_fs = Q.store_thm("extract_stdo_extract_fs",
  `∀io_events fs init out ll.
   stdo fd nm fs init ∧ fd < 256 ∧ ALOOKUP fs.infds
   extract_fs fs io_events = SOME (add_stdo fd nm fs out with numchars := ll) ⇒
   extract_stdo (n2w fd) io_events = out`,
  Induct \\ simp[extract_fs_def,extract_stdo_def]
  >- (
    rpt gen_tac
    \\ simp[GSYM AND_IMP_INTRO] \\ strip_tac
    \\ simp[add_stdo_def,up_stdo_def]
    \\ SELECT_ELIM_TAC
    \\ conj_tac >- metis_tac[]
    \\ simp[stdo_def]
    \\ simp[fsupdate_numchars]
    \\ simp[fsupdate_def]
    \\ rw[IO_fs_component_equality]
    \\ qpat_assum`ALOOKUP fs.files _ = _`mp_tac
    \\ qpat_assum`fs.files = _`SUBST1_TAC
    \\ simp[ALIST_FUPDKEY_ALOOKUP] )
  \\ Cases
  \\ rw[extract_fs_def,extract_stdo_def]
  >- (
    fs[option_caseeq,pair_caseeq]
    \\ fs[] \\ fs[fs_ffi_part_def]
    \\ rveq
    \\ fs[ffi_write_def]
    \\ fs[OPTION_CHOICE_EQUALS_OPTION,UNCURRY] \\ rveq
    \\ TRY ( Cases_on`l0` \\ fs[LUPDATE_def] \\ NO_TAC )
    \\ qmatch_asmsub_abbrev_tac`extract_fs fs'`
    \\ first_x_assum(qspec_then`fs'`mp_tac)
    \\ simp[]
    \\ fs[write_def,UNCURRY]
    \\ rveq \\ fs[]
    \\ Cases_on`l0` \\ fs[]
    \\ Cases_on`t` \\ fs[]
    \\ Cases_on`t'` \\ fs[]
    \\ fs[LUPDATE_compute]
    \\ Cases_on`h` \\ fs[] \\ rveq
    \\ fs[stdo_def]
    \\ simp[Abbr`fs'`,fsupdate_def]
    \\ CASE_TAC \\ fs[]
    \\ simp[ALIST_FUPDKEY_ALOOKUP]

    \\ cheat)
  \\ qpat_x_assum`_ = SOME _`mp_tac
  \\ simp[option_caseeq,pair_caseeq]
  \\ qhdtm_x_assum`stdo`mp_tac
  \\ simp[fs_ffi_part_def]
  \\ simp[stdo_def]
  \\ simp[bool_case_eq]
  \\ rw[] \\ fs[]
  stdo_def

val is_write_def = Define`
  (is_write fd (IO_event name _ ((fd',st)::_)) ⇔ name="write" ∧ fd' = fd ∧ st = 0w) ∧
  (is_write _ _ ⇔ F)`;
val _ = export_rewrites["is_write_def"];

val extract_write_def = Define`
  extract_write (IO_event _ _ (_::(_,nw)::bytes)) = TAKE (w2n nw) (MAP FST bytes)`;
val _ = export_rewrites["extract_write_def"];

val extract_writes_def = Define
  `extract_writes fd io_events =
     FLAT (MAP extract_write (FILTER (is_write fd) io_events))`;
val _ = overload_on("extract_stdout",``extract_writes 1w``);
val _ = overload_on("extract_stderr",``extract_writes 2w``);

val extract_writes_thm = Q.store_thm("extract_writes_thm",
  `extract_fs init_fs io_events = SOME fs ∧
   get_file_content init_fs = SOME (init,pos)
   ⇒
  `,
  type_of``get_file_content``
ffi_write_def
write_def
fs_ffi_part_def
ffi_read_def
read_def

val extract_stdout_def = Define`
  extract_stdout io_events =
    @out.
      ∀fs. wfFS fs ∧ STD_streams fs ⇒
          ∃ll. extract_fs fs io_events = SOME (add_stdout fs out with numchars := ll)`;

val extract_stdout_intro = Q.store_thm("extract_stdout_intro",
  `wfFS fs ∧ STD_streams fs ∧
   extract_fs fs io_events = SOME (add_stdout fs out with numchars := ll) ⇒
   extract_stdout io_events = out`,
  rw[extract_stdout_def]
  \\ SELECT_ELIM_TAC \\ reverse(rw[])
  >- (
    first_x_assum(qspec_then`fs`mp_tac)
    \\ rw[]
    \\ imp_res_tac STD_streams_stdout
    \\ imp_res_tac stdo_add_stdo
    \\ metis_tac[stdo_UNICITY_R,stdo_numchars,APPEND_11] )
  \\ qexists_tac`out`
  \\ rw[]
  \\ Induct_on`io_events`
  \\ rw[extract_fs_def]
  >- cheat
  \\ Cases_on`h` \\ fs[extract_fs_def]
  \\ rw[] \\ fs[]
  \\ pop_assum mp_tac \\ CASE_TAC
  \\ CASE_TAC \\ rw[]
*)

(*-------------------------------------------------------------------------------------------------*)

(*These theorems are need to be remade to use cfMain for projs, oracle or ffi that aren't basis_ffi*)

(* TODO: remove? *)

(* the failure of an fs ffi call doesn't depend on the filesystem
val fs_ffi_NONE_irrel = Q.store_thm("fs_ffi_NONE_irrel",
 `!f. f ∈ {ffi_read; ffi_write; ffi_open_in; ffi_open_out; ffi_close} ∧
      f bytes fs = NONE ⇒ f bytes fs' = NONE`,
  rw[] >>
  fs[ffi_read_def,ffi_write_def,ffi_open_in_def,ffi_open_out_def,ffi_close_def] >>
  every_case_tac >> fs[OPTION_CHOICE_EQ_NONE]); *)

(*RTC_call_FFI_rel_IMP_basis_events show that extracting output from two ffi_states will use the
  same function if the two states are related by a series of FFI_calls. If this is the case for
  your oracle (and projs), then this proof should be relatively similar. Note
  that to make the subsequent proofs similar one should show an equivalence between
  extract_output and proj1  *)
val RTC_call_FFI_rel_IMP_basis_events = Q.store_thm ("RTC_call_FFI_rel_IMP_basis_events",
  `!fs st st'. call_FFI_rel^* st st' ==> st.oracle = basis_ffi_oracle ==>
  (extract_fs_with_numchars fs st.io_events
     = fsFFI$decode (basis_proj1 st.ffi_state ' "write") ==>
   extract_fs_with_numchars fs st'.io_events
     = fsFFI$decode (basis_proj1 st'.ffi_state ' "write"))`,
  strip_tac
  \\ HO_MATCH_MP_TAC RTC_INDUCT \\ rw [] \\ fs []
  \\ fs [evaluatePropsTheory.call_FFI_rel_def]
  \\ fs [ffiTheory.call_FFI_def]
  \\ Cases_on `st.final_event = NONE` \\ fs [] \\ rw []
  \\ Cases_on `n = ""` \\ fs [] THEN1 (rveq \\ fs [])
  \\ FULL_CASE_TAC \\ fs [] \\ rw [] \\ fs []
  \\ FULL_CASE_TAC \\ fs [] \\ rw [] \\ fs []
  \\ Cases_on `f` \\ fs []
  \\ fs [extract_fs_with_numchars_APPEND,extract_fs_with_numchars_def,basis_proj1_write] \\ rfs []
  \\ first_x_assum match_mp_tac
  \\ qpat_x_assum`_ = Oracle_return _ _`mp_tac
  \\ simp[basis_ffi_oracle_def,fs_ffi_part_def]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ rpt(full_case_tac \\ fs[option_eq_some,MAP_ZIP] \\ rw[]) >>
  rfs[MAP_ZIP]);

(* the first condition for the previous theorem holds for the
  init_state ffi  *)
val extract_fs_basis_ffi = Q.store_thm ("extract_fs_basis_ffi",
  `!ll. extract_fs fs (basis_ffi cls fs).io_events =
   decode (basis_proj1 (basis_ffi cls fs).ffi_state ' "write")`,
  rw[ml_progTheory.init_state_def,extract_fs_def,extract_fs_with_numchars_def,
     basis_ffi_def,basis_proj1_write,IO_fs_component_equality]);

val append_hprop = Q.store_thm ("append_hprop",
  `A s1 /\ B s2 ==> DISJOINT s1 s2 ==> (A * B) (s1 ∪ s2)`,
  rw[set_sepTheory.STAR_def] \\ SPLIT_TAC
);

val iobuff_loc_num =
  TextIOProgTheory.iobuff_loc_def
  |> concl |> rhs |> rand;

val IOFS_precond = Q.prove(
  `wfFS fs ⇒ LENGTH v >= 2052 ⇒
   IOFS fs
    ({FFI_part (encode fs) (mk_ffi_next fs_ffi_part) (MAP FST (SND(SND fs_ffi_part))) events}
    ∪ {Mem ^iobuff_loc_num (W8array v)})`,
  rw[IOFS_def,cfHeapsBaseTheory.IOx_def,fs_ffi_part_def,cfHeapsBaseTheory.IO_def,one_def,
     IOFS_iobuff_def,W8ARRAY_def,cell_def]
  \\ rw[set_sepTheory.SEP_EXISTS_THM,set_sepTheory.cond_STAR,set_sepTheory.SEP_CLAUSES,
        TextIOProgTheory.iobuff_loc_def]
  \\ qexists_tac`events` \\  qexists_tac`v` \\ exists_tac iobuff_loc_num
  \\ fs[SEP_CLAUSES,one_STAR,one_def,append_hprop]
  )|> UNDISCH_ALL;

val STDIO_precond = Q.prove(
` wfFS fs ==>
  STD_streams fs ==>
  LENGTH v >= 2052 ==>
  STDIO fs
    ({FFI_part (encode fs)
               (mk_ffi_next fs_ffi_part) (MAP FST (SND(SND fs_ffi_part))) events}
     ∪ {Mem ^iobuff_loc_num (W8array v)})`,
  rw[STDIO_def,IOFS_precond,SEP_EXISTS_THM,SEP_CLAUSES] >>
  qexists_tac`fs.numchars` >>
  mp_tac (IOFS_precond |> DISCH_ALL |> GEN ``fs : IO_fs``)>>
  cases_on`fs` >> fs[IO_fs_numchars_fupd]
  ) |> UNDISCH_ALL |> curry save_thm "STDIO_precond";

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

val whole_prog_spec_def = Define`
  whole_prog_spec fv cl fs post ⇔
    ∃fs'.
    app (basis_proj1, basis_proj2) fv [Conv NONE []]
      (COMMANDLINE cl * STDIO fs)
      (POSTv uv. &UNIT_TYPE () uv * STDIO fs') ∧
    post (fs' with numchars := fs.numchars)`;

val whole_prog_spec_semantics_prog = Q.store_thm("whole_prog_spec_semantics_prog",
  `∀fname fv.
     ML_code env1 (init_state (basis_ffi cl fs)) prog NONE env2 st2 ==>
     lookup_var fname env2 = SOME fv ==>
     whole_prog_spec fv cl fs Q ==>
     no_dup_mods (SNOC ^main_call prog) (init_state (basis_ffi cl fs)).defined_mods /\
     no_dup_top_types (SNOC ^main_call prog) (init_state (basis_ffi cl fs)).defined_types ==>
     (?h1 h2. SPLIT (st2heap (basis_proj1, basis_proj2) st2) (h1,h2) /\ (COMMANDLINE cl * STDIO fs) h1)
   ==>
   ∃io_events fs'.
     semantics_prog (init_state (basis_ffi cl fs)) env1
       (SNOC ^main_call prog) (Terminate Success io_events) /\
     extract_fs fs io_events = SOME fs' ∧ Q fs'`,
  rw[whole_prog_spec_def]
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

val heap_thms = [COMMANDLINE_precond, STDIO_precond];

fun build_set [] = raise(ERR"subset_basis_st""no STDOUT in precondition")
  | build_set [th] = th
  | build_set (th1::th2::ths) =
      let
        val th = MATCH_MP append_hprop (CONJ th1 th2)
        val th = CONV_RULE(LAND_CONV EVAL)th
        val th = MATCH_MP th TRUTH |> SIMP_RULE (srw_ss()) [UNION_EMPTY]
        val th = (CONV_RULE(RAND_CONV (pred_setLib.UNION_CONV EVAL)) th
        handle _ => th) (* TODO quick fix *)
      in build_set (th::ths) end

val sets_thm = build_set heap_thms |> curry save_thm "sets_thm";

val basis_ffi_length_thms = save_thm("basis_ffi_length_thms", LIST_CONJ
[ffi_write_length,ffi_read_length,ffi_open_in_length,ffi_open_out_length,
 ffi_close_length, clFFITheory.ffi_get_arg_count_length,
 clFFITheory.ffi_get_arg_length_length,  clFFITheory.ffi_get_arg_length ]);

val basis_ffi_part_defs = save_thm("basis_ffi_part_defs", LIST_CONJ
[fs_ffi_part_def,clFFITheory.cl_ffi_part_def]);

(* This is used to show to show one of the parts of parts_ok for the state after a spec *)
val oracle_parts = Q.store_thm("oracle_parts",
  `!st. st.ffi.oracle = basis_ffi_oracle /\ MEM (ns, u) basis_proj2 /\ MEM m ns /\ u m conf bytes (basis_proj1 x ' m) = SOME (new_bytes, w)
    ==> (?y. st.ffi.oracle m x conf bytes = Oracle_return y new_bytes /\ basis_proj1 x
 |++ MAP (\n. (n,w)) ns = basis_proj1 y)`,
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
  \\ CCONTR_TAC \\ fs[] \\ rfs[]);

val parts_ok_basis_st = Q.store_thm("parts_ok_basis_st",
  `parts_ok (auto_state_1 (basis_ffi cls fs)).ffi (basis_proj1, basis_proj2)` ,
  qmatch_goalsub_abbrev_tac`st.ffi`
  \\ `st.ffi.oracle = basis_ffi_oracle`
  by( simp[Abbr`st`] \\ EVAL_TAC \\ NO_TAC)
  \\ rw[cfStoreTheory.parts_ok_def]
  \\ TRY ( simp[Abbr`st`] \\ EVAL_TAC \\ NO_TAC )
  \\ TRY ( imp_res_tac oracle_parts \\ rfs[] \\ NO_TAC)
  \\ qpat_x_assum`MEM _ basis_proj2`mp_tac
  \\ simp[basis_proj2_def,basis_ffi_part_defs,cfHeapsBaseTheory.mk_proj2_def]
  \\ TRY (qpat_x_assum`_ = SOME _`mp_tac)
  \\ simp[basis_proj1_def,basis_ffi_part_defs,cfHeapsBaseTheory.mk_proj1_def,FUPDATE_LIST_THM]
  \\ rw[] \\ rw[] \\ pairarg_tac \\ fs[FLOOKUP_UPDATE] \\ rw[]
  \\ fs[FAPPLY_FUPDATE_THM,cfHeapsBaseTheory.mk_ffi_next_def]
  \\ TRY pairarg_tac \\ fs[]
  \\ EVERY (map imp_res_tac (CONJUNCTS basis_ffi_length_thms)) \\ fs[]
  \\ srw_tac[DNF_ss][]
);

(* TODO: move somewhere else? *)
val SPLIT_exists = Q.store_thm ("SPLIT_exists",
  `(A * B) s /\ s ⊆ C
    ==> (?h1 h2. SPLIT C (h1, h2) /\ (A * B) h1)`,
  rw[]
  \\ qexists_tac `s` \\ qexists_tac `C DIFF s`
  \\ SPLIT_TAC
);

val _ = export_theory();
