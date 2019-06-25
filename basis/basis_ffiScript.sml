(*
  Instantiate the CakeML FFI oracle for the oracle of the basis library.
*)
open preamble ml_translatorTheory ml_translatorLib ml_progLib
     cfLib basisFunctionsLib set_sepTheory
     fsFFITheory fsFFIPropsTheory
     CommandLineProofTheory TextIOProofTheory
     runtimeFFITheory RuntimeProofTheory

val _ = new_theory"basis_ffi";

(*---------------------------------------------------------------------------*)
(* GENERALISED FFI *)

val basis_ffi_oracle_def = Define `
  basis_ffi_oracle =
    \name (cls,fs) conf bytes.
     if name = "write" then
       case ffi_write conf bytes fs of
       | SOME(FFIreturn bytes fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_final FFI_failed else
     if name = "read" then
       case ffi_read conf bytes fs of
       | SOME(FFIreturn bytes fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_final FFI_failed else
     if name = "get_arg_count" then
       case ffi_get_arg_count conf bytes cls of
       | SOME(FFIreturn bytes cls) => Oracle_return (cls,fs) bytes
       | _ => Oracle_final FFI_failed else
     if name = "get_arg_length" then
       case ffi_get_arg_length conf bytes cls of
       | SOME(FFIreturn bytes cls) => Oracle_return (cls,fs) bytes
       | _ => Oracle_final FFI_failed else
     if name = "get_arg" then
       case ffi_get_arg conf bytes cls of
       | SOME(FFIreturn bytes cls) => Oracle_return (cls,fs) bytes
       | _ => Oracle_final FFI_failed else
     if name = "open_in" then
       case ffi_open_in conf bytes fs of
       | SOME(FFIreturn bytes fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_final FFI_failed else
     if name = "open_out" then
       case ffi_open_out conf bytes fs of
       | SOME(FFIreturn bytes fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_final FFI_failed else
     if name = "close" then
       case ffi_close conf bytes fs of
       | SOME(FFIreturn bytes fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_final FFI_failed else
     if name = "exit" then
       case ffi_exit conf bytes () of
       | SOME(FFIreturn bytes ()) => Oracle_return (cls,fs) bytes
       | SOME(FFIdiverge) => Oracle_final FFI_diverged
       | NONE => Oracle_final FFI_failed else
     Oracle_final FFI_failed`

(* standard streams are initialized *)
val basis_ffi_def = Define `
  basis_ffi cl fs =
    <| oracle := basis_ffi_oracle
     ; ffi_state := (cl, fs)
     ; io_events := [] |>`;

val basis_proj1_def = Define `
  basis_proj1 = (λ(cls, fs).
    FEMPTY |++ ((mk_proj1 cl_ffi_part cls)
                ++ (mk_proj1 fs_ffi_part fs)
                ++ (mk_proj1 runtime_ffi_part ()
                )))`;

val basis_proj2_def = Define `
  basis_proj2 =
    [mk_proj2 cl_ffi_part;
     mk_proj2 fs_ffi_part;
     mk_proj2 runtime_ffi_part]`;

Theorem basis_proj1_write:
   basis_proj1 ffi ' "write" = encode(SND ffi)
Proof
  PairCases_on`ffi` \\ EVAL_TAC
QED

(* builds the file system from a list of events *)

val extract_fs_with_numchars_def = Define `
  (extract_fs_with_numchars init_fs [] = SOME init_fs) ∧
  (extract_fs_with_numchars init_fs ((IO_event name conf bytes)::xs) =
    case (ALOOKUP (SND(SND fs_ffi_part)) name) of
    | SOME ffi_fun => (case ffi_fun conf (MAP FST bytes) init_fs of
                       | SOME (FFIreturn bytes' fs') =>
                         if bytes' = MAP SND bytes then
                           extract_fs_with_numchars fs' xs
                         else NONE
                       | _ => NONE)
    | NONE => extract_fs_with_numchars init_fs xs)`

Theorem extract_fs_with_numchars_APPEND:
   !xs ys init_fs. extract_fs_with_numchars init_fs (xs ++ ys) =
    case extract_fs_with_numchars init_fs xs of
    | NONE => NONE
    | SOME fs => extract_fs_with_numchars fs ys
Proof
  Induct_on`xs` \\ simp[extract_fs_with_numchars_def]
  \\ Cases \\ simp[extract_fs_with_numchars_def]
  \\ CASE_TAC
  \\ rpt gen_tac
  \\ rpt CASE_TAC
QED

val extract_fs_def = Define`
  extract_fs init_fs events =
    OPTION_MAP (numchars_fupd (K init_fs.numchars))
    (extract_fs_with_numchars init_fs events)`;

Theorem extract_fs_with_numchars_keeps_iostreams:
   ∀ls fs fs' off.
   (extract_fs_with_numchars fs ls = SOME fs') ∧
   (ALOOKUP fs'.infds fd = SOME(UStream nm, md, off)) ⇒
   ∃off'.
     (ALOOKUP fs.infds fd = SOME (UStream nm, md, off')) ∧ off' ≤ off ∧
     (∀content.
       (ALOOKUP fs.inode_tbl (UStream nm) = SOME content) ∧ (off' = LENGTH content) ∧
       (∀fd' md' off'. (ALOOKUP fs.infds fd' = SOME (UStream nm, md', off')) ⇒ (fd = fd'))
       ⇒
       ∃written.
         (ALOOKUP fs'.inode_tbl (UStream nm) = SOME (content ++ written)) ∧
         (off = off' + LENGTH written))
Proof
  Induct
  >- ( rw[extract_fs_with_numchars_def])
  \\ Cases
  \\ rw[extract_fs_with_numchars_def]
  \\ fs[CaseEq"option",CaseEq"ffi_result"]
  \\ fs[fsFFITheory.fs_ffi_part_def]
  \\ last_x_assum drule
  \\ disch_then drule
  \\ strip_tac \\ rveq
  \\ reverse(fs[CaseEq"bool"]) \\ rveq \\ fs[]
  \\ fs[fsFFITheory.ffi_open_in_def,
        fsFFITheory.ffi_open_out_def,
        fsFFITheory.ffi_write_def,
        fsFFITheory.ffi_read_def,
        fsFFITheory.ffi_close_def]
  \\ fs[OPTION_CHOICE_EQUALS_OPTION, CaseEq"list"]
  \\ TRY pairarg_tac \\ fs[] \\ rveq \\ fs[]
  \\ fs[fsFFITheory.closeFD_def,
        fsFFITheory.read_def,
        fsFFITheory.openFile_truncate_def,
        fsFFITheory.openFile_def,
        fsFFITheory.write_def]
  \\ TRY pairarg_tac \\ fs[]
  \\ rveq \\ fs[ALOOKUP_ADELKEY, fsFFIPropsTheory.bumpFD_forwardFD]
  \\ fs[CaseEq"bool"]
  \\ rfs[fsFFITheory.fsupdate_def, fsFFIPropsTheory.forwardFD_def, AFUPDKEY_ALOOKUP]
  \\ fs[CaseEq"option"]
  \\ fs[CaseEq"bool"]
  \\ Cases_on`v` \\ fs[]
  \\ rveq \\ fs[] \\ rfs[]
  \\ rw[] \\ fs[]
  \\ TRY(
    fsrw_tac[DNF_ss][] \\ fs[DISJ_EQ_IMP]
    \\ NO_TAC)
  >- (
    Cases_on`fnm = UStream nm` \\ fsrw_tac[DNF_ss][]
    \\ fs[FORALL_PROD] \\ rveq \\ fs[] \\ rfs[]
    \\ metis_tac[] )
  \\ fsrw_tac[DNF_ss][FORALL_PROD]
QED

Theorem extract_fs_with_numchars_closes_iostreams:
   ∀ls fs fs' fd nm off.
   (extract_fs_with_numchars fs ls = SOME fs') ∧
   (∀fd off. ALOOKUP fs.infds fd ≠ SOME(UStream nm, md, off))
   ⇒
   (ALOOKUP fs'.infds fd ≠ SOME(UStream nm, md, off))
Proof
  Induct
  >- (
    rw[extract_fs_with_numchars_def]
    \\ metis_tac[] )
  \\ Cases
  \\ rw[extract_fs_with_numchars_def]
  \\ fs[CaseEq"option",CaseEq"ffi_result"]
  >- metis_tac[]
  \\ fs[fsFFITheory.fs_ffi_part_def]
  \\ last_x_assum drule
  \\ disch_then match_mp_tac
  \\ reverse(fs[CaseEq"bool"]) \\ rveq \\ fs[]
  \\ fs[fsFFITheory.ffi_open_in_def,
        fsFFITheory.ffi_open_out_def,
        fsFFITheory.ffi_write_def,
        fsFFITheory.ffi_read_def,
        fsFFITheory.ffi_close_def]
  \\ fs[OPTION_CHOICE_EQUALS_OPTION, CaseEq"list"]
  \\ TRY pairarg_tac \\ fs[] \\ rveq \\ fs[]
  \\ fs[fsFFITheory.closeFD_def,
        fsFFITheory.read_def,
        fsFFITheory.openFile_truncate_def,
        fsFFITheory.openFile_def,
        fsFFITheory.write_def]
  \\ TRY pairarg_tac \\ fs[]
  \\ rveq \\ fs[ALOOKUP_ADELKEY, fsFFITheory.bumpFD_def, AFUPDKEY_ALOOKUP]
  \\ rw[fsFFITheory.fsupdate_def, AFUPDKEY_ALOOKUP]
  \\ PURE_CASE_TAC \\ fs[CaseEq"option"]
  \\ CCONTR_TAC \\ fs[]
QED

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

Theorem extract_stdo_extract_fs
  `∀io_events fs init out ll.
   stdo fd nm fs init ∧ fd < 256 ∧ ALOOKUP fs.infds
   extract_fs fs io_events = SOME (add_stdo fd nm fs out with numchars := ll) ⇒
   extract_stdo (n2w fd) io_events = out`
  (Induct \\ simp[extract_fs_def,extract_stdo_def]
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
    \\ qpat_assum`ALOOKUP fs.inode_tbl _ = _`mp_tac
    \\ qpat_assum`fs.inode_tbl = _`SUBST1_TAC
    \\ simp[AFUPDKEY_ALOOKUP] )
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
    \\ simp[AFUPDKEY_ALOOKUP]

    \\ ...)
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

Theorem extract_writes_thm
  `extract_fs init_fs io_events = SOME fs ∧
   get_file_content init_fs = SOME (init,pos)
   ⇒
  `
  (type_of``get_file_content``
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

Theorem extract_stdout_intro
  `wfFS fs ∧ STD_streams fs ∧
   extract_fs fs io_events = SOME (add_stdout fs out with numchars := ll) ⇒
   extract_stdout io_events = out`
  (rw[extract_stdout_def]
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
  >- ...
  \\ Cases_on`h` \\ fs[extract_fs_def]
  \\ rw[] \\ fs[]
  \\ pop_assum mp_tac \\ CASE_TAC
  \\ CASE_TAC \\ rw[]
*)

(*-------------------------------------------------------------------------------------------------*)

(*These theorems are need to be remade to use cfMain for projs, oracle or ffi that aren't basis_ffi*)

(* TODO: remove? *)

(* the failure of an fs ffi call doesn't depend on the filesystem
Theorem fs_ffi_NONE_irrel:
  !f. f ∈ {ffi_read; ffi_write; ffi_open_in; ffi_open_out; ffi_close} ∧
      f bytes fs = NONE ⇒ f bytes fs' = NONE
Proof
  rw[] >>
  fs[ffi_read_def,ffi_write_def,ffi_open_in_def,ffi_open_out_def,ffi_close_def] >>
  every_case_tac >> fs[OPTION_CHOICE_EQ_NONE]
QED *)

(*RTC_call_FFI_rel_IMP_basis_events show that extracting output from two ffi_states will use the
  same function if the two states are related by a series of FFI_calls. If this is the case for
  your oracle (and projs), then this proof should be relatively similar. Note
  that to make the subsequent proofs similar one should show an equivalence between
  extract_output and proj1  *)
Theorem RTC_call_FFI_rel_IMP_basis_events:
   !fs st st'. call_FFI_rel^* st st' ==> st.oracle = basis_ffi_oracle ==>
  (extract_fs_with_numchars fs st.io_events
     = fsFFI$decode (basis_proj1 st.ffi_state ' "write") ==>
   extract_fs_with_numchars fs st'.io_events
     = fsFFI$decode (basis_proj1 st'.ffi_state ' "write"))
Proof
  strip_tac
  \\ HO_MATCH_MP_TAC RTC_INDUCT \\ rw [] \\ fs []
  \\ fs [evaluatePropsTheory.call_FFI_rel_def]
  \\ fs [ffiTheory.call_FFI_def]
(*  \\ Cases_on `st.final_event = NONE` \\ fs [] \\ rw []*)
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
  rfs[MAP_ZIP]
QED

(* the first condition for the previous theorem holds for the
  init_state ffi  *)
Theorem extract_fs_basis_ffi:
   !ll. extract_fs fs (basis_ffi cls fs).io_events =
   decode (basis_proj1 (basis_ffi cls fs).ffi_state ' "write")
Proof
  rw[ml_progTheory.init_state_def,extract_fs_def,extract_fs_with_numchars_def,
     basis_ffi_def,basis_proj1_write,IO_fs_component_equality]
QED

Theorem append_hprop:
   A s1 /\ B s2 ==> DISJOINT s1 s2 ==> (A * B) (s1 ∪ s2)
Proof
  rw[set_sepTheory.STAR_def] \\ SPLIT_TAC
QED

val iobuff_loc_num =
  TextIOProgTheory.iobuff_loc_def
  |> concl |> rhs |> rand;

Theorem IOFS_precond = Q.prove(`
  wfFS fs ⇒ LENGTH v >= 2052 ⇒
   IOFS fs
    ({FFI_part (encode fs) (mk_ffi_next fs_ffi_part) (MAP FST (SND(SND fs_ffi_part))) events}
    ∪ {Mem ^iobuff_loc_num (W8array v)})`,
  rw[IOFS_def,cfHeapsBaseTheory.IOx_def,fs_ffi_part_def,cfHeapsBaseTheory.IO_def,one_def,
     IOFS_iobuff_def,W8ARRAY_def,cell_def]
  \\ rw[set_sepTheory.SEP_EXISTS_THM,set_sepTheory.cond_STAR,set_sepTheory.SEP_CLAUSES,
        TextIOProgTheory.iobuff_loc_def]
  \\ qexists_tac`events` \\  qexists_tac`v` \\ exists_tac iobuff_loc_num
  \\ fs[SEP_CLAUSES,one_STAR,one_def,append_hprop])|> UNDISCH_ALL;

Theorem STDIO_precond = Q.prove(`
 wfFS fs ==>
  STD_streams fs ==>
  LENGTH v >= 2052 ==>
  STDIO fs
    ({FFI_part (encode fs)
               (mk_ffi_next fs_ffi_part) (MAP FST (SND(SND fs_ffi_part))) events}
     ∪ {Mem ^iobuff_loc_num (W8array v)})`,
  rw[STDIO_def,IOFS_precond,SEP_EXISTS_THM,SEP_CLAUSES] >>
  qexists_tac`fs.numchars` >>
  mp_tac (IOFS_precond |> DISCH_ALL |> GEN ``fs : IO_fs``)>>
  cases_on`fs` >> fs[IO_fs_numchars_fupd]) |> UNDISCH_ALL |> curry save_thm "STDIO_precond";

Theorem RUNTIME_precond:
   RUNTIME {FFI_part (encode ()) (mk_ffi_next runtime_ffi_part)
           (MAP FST (SND(SND runtime_ffi_part))) events}
Proof
  rw[RUNTIME_def,runtimeFFITheory.runtime_ffi_part_def,
     IOx_def,SEP_EXISTS_THM,SEP_CLAUSES,IO_def,one_def]
QED

(*call_main_thm_basis uses call_main_thm2 to get Semantics_prog, and then uses the previous two
  theorems to prove the outcome of extract_output. If RTC_call_FFI_rel_IMP* uses proj1, after
  showing that post-condition which gives effects your programs output is an FFI_part and
  assuming that parts_ok is satisfied, an assumption about proj1 and the ffi_state should be
  derived which should fit the function on some st.ffi_state which returns extract_output on
  st.io_events  *)

fun mk_main_call s =
  ``(Dlet unknown_loc (Pcon NONE []) (App Opapp [Var (Short ^s); Con NONE []]))``;
val fname = mk_var("fname",``:string``);
val main_call = mk_main_call fname;

val whole_prog_spec_def = Define`
  whole_prog_spec fv cl fs sprop post ⇔
    ∃fs'.
    app (basis_proj1, basis_proj2) fv [Conv NONE []]
      (COMMANDLINE cl * STDIO fs * case sprop of NONE => &T | SOME p => p)
      (POSTv uv. &UNIT_TYPE () uv * STDIO fs') ∧
    post (fs' with numchars := fs.numchars)`;

val whole_prog_ffidiv_spec_def = Define`
  whole_prog_ffidiv_spec fv cl fs post ⇔
    ∃fs' n' c' b'.
    app (basis_proj1, basis_proj2) fv [Conv NONE []]
      (COMMANDLINE cl * STDIO fs * RUNTIME)
      (POSTf n. λc b. STDIO fs' * RUNTIME * &(n = n' /\ c = c' /\ b = b')) ∧
    post n' c' b' (fs' with numchars := fs.numchars)`;

Theorem whole_prog_spec_semantics_prog:
   ∀fname fv.
     Decls env1 (init_state (basis_ffi cl fs)) prog env2 st2 ==>
     lookup_var fname env2 = SOME fv ==>
     whole_prog_spec fv cl fs sprop Q ==>
     (?h1 h2. SPLIT (st2heap (basis_proj1, basis_proj2) st2) (h1,h2) /\
     (COMMANDLINE cl * STDIO fs * case sprop of NONE => &T | SOME Q => Q) h1)
   ==>
   ∃io_events fs'.
     semantics_prog (init_state (basis_ffi cl fs)) env1
       (SNOC ^main_call prog) (Terminate Success io_events) /\
     extract_fs fs io_events = SOME fs' ∧ Q fs'
Proof
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
QED

Theorem whole_prog_spec_semantics_prog_ffidiv:
   ∀fname fv.
     Decls env1 (init_state (basis_ffi cl fs)) prog env2 st2 ==>
     lookup_var fname env2 = SOME fv ==>
     whole_prog_ffidiv_spec fv cl fs Q ==>
     (?h1 h2. SPLIT (st2heap (basis_proj1, basis_proj2) st2) (h1,h2) /\
     (COMMANDLINE cl * STDIO fs * RUNTIME) h1)
   ==>
   ∃io_events fs' n c b.
     semantics_prog (init_state (basis_ffi cl fs)) env1
       (SNOC ^main_call prog)
       (Terminate (FFI_outcome(Final_event n c b FFI_diverged)) io_events) /\
     extract_fs fs io_events = SOME fs' ∧ Q n c b fs'
Proof
  rw[whole_prog_ffidiv_spec_def]
  \\ drule (GEN_ALL call_main_thm2_ffidiv)
  \\ rpt(disch_then drule)
  \\ disch_then (qspecl_then [`basis_proj2`,`basis_proj1`] mp_tac)
  \\ disch_then (qspecl_then [`h2`, `h1`] mp_tac)
  \\ disch_then (qspec_then `\n c b. STDIO fs' * RUNTIME * &(n = n' ∧ c = c' ∧ b = b')` mp_tac)
  \\ disch_then (qspec_then `COMMANDLINE cl * STDIO fs * RUNTIME` mp_tac)
  \\ simp[] \\ strip_tac
  \\ asm_exists_tac \\ rw[]
  \\ rw[extract_fs_def,PULL_EXISTS]
  \\ drule RTC_call_FFI_rel_IMP_basis_events
  \\ simp[Once ml_progTheory.init_state_def,Once basis_ffi_def]
  \\ simp[Once ml_progTheory.init_state_def,Once basis_ffi_def]
  \\ simp[Once extract_fs_with_numchars_def]
  \\ simp[Once ml_progTheory.init_state_def]
  \\ rw[basis_proj1_write,Once basis_ffi_def]
  \\ `n = n' /\ c = c' /\ b = b'` by(fs[STAR_def,cond_def])
  \\ rveq
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
QED

val basis_ffi_length_thms = save_thm("basis_ffi_length_thms",
  LIST_CONJ
    [ffi_write_length,ffi_read_length,ffi_open_in_length,ffi_open_out_length,
     ffi_close_length, clFFITheory.ffi_get_arg_count_length,
     clFFITheory.ffi_get_arg_length_length,  clFFITheory.ffi_get_arg_length,
     ffi_exit_length]);

val basis_ffi_part_defs = save_thm("basis_ffi_part_defs",
  LIST_CONJ
    [fs_ffi_part_def,clFFITheory.cl_ffi_part_def,runtime_ffi_part_def]);

(* This is used to show to show one of the parts of parts_ok for the state after a spec *)
Theorem oracle_parts:
   !st.
     st.ffi.oracle = basis_ffi_oracle /\
     MEM (ns, u) basis_proj2 /\
     MEM m ns /\
     u m conf bytes (basis_proj1 x ' m) = SOME (FFIreturn new_bytes w)
     ==>
     (?y. st.ffi.oracle m x conf bytes = Oracle_return y new_bytes /\
          basis_proj1 x |++ MAP (\n. (n,w)) ns = basis_proj1 y)
Proof
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
  \\ TRY (
      fs[ffi_exit_def] \\ NO_TAC)
  \\ disj2_tac
  \\ CCONTR_TAC \\ fs[] \\ rfs[]
QED

(* TODO: move to fsFFI? *)
Theorem fs_ffi_no_ffi_div:
    (ffi_open_in conf bytes fs = SOME FFIdiverge ==> F) /\
  (ffi_open_out conf bytes fs = SOME FFIdiverge ==> F) /\
  (ffi_read conf bytes fs = SOME FFIdiverge ==> F) /\
  (ffi_close conf bytes fs = SOME FFIdiverge ==> F) /\
  (ffi_write conf bytes fs = SOME FFIdiverge ==> F)
Proof
  rw[ffi_open_in_def,ffi_open_out_def,ffi_read_def,ffi_close_def,ffi_write_def,
     OPTION_GUARD_COND,OPTION_CHOICE_EQUALS_OPTION,ELIM_UNCURRY]
  \\ rpt(PURE_TOP_CASE_TAC \\ rw[])
  \\ rw[OPTION_CHOICE_EQUALS_OPTION,ELIM_UNCURRY]
QED

(* TODO: move to clFFI? *)
Theorem cl_ffi_no_ffi_div:
    (ffi_get_arg_count conf bytes cls = SOME FFIdiverge ==> F) /\
  (ffi_get_arg_length conf bytes cls = SOME FFIdiverge ==> F) /\
  (ffi_get_arg conf bytes cls = SOME FFIdiverge ==> F)
Proof
  rw[clFFITheory.ffi_get_arg_count_def,clFFITheory.ffi_get_arg_length_def,
     clFFITheory.ffi_get_arg_def]
QED

Theorem oracle_parts_div:
   !st.
     st.ffi.oracle = basis_ffi_oracle /\ MEM (ns, u) basis_proj2 /\
     MEM m ns /\
     u m conf bytes (basis_proj1 x ' m) = SOME FFIdiverge
     ==>
     st.ffi.oracle m x conf bytes = Oracle_final FFI_diverged
Proof
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
  \\ fs[cl_ffi_no_ffi_div,fs_ffi_no_ffi_div]
  \\ disj2_tac
  \\ CCONTR_TAC \\ fs[] \\ rfs[]
QED

val _ = translation_extends "TextIOProg";
val st_f = get_ml_prog_state () |> get_state |> strip_comb |> fst;
val st = mk_icomb (st_f, ``basis_ffi cls fs``);
val _ = reset_translation ()

Theorem parts_ok_basis_st:
   parts_ok (^st).ffi (basis_proj1, basis_proj2)
Proof
  qmatch_goalsub_abbrev_tac`st.ffi`
  \\ `st.ffi.oracle = basis_ffi_oracle`
  by( simp[Abbr`st`] \\ EVAL_TAC \\ NO_TAC)
  \\ rw[cfStoreTheory.parts_ok_def]
  \\ TRY ( simp[Abbr`st`] \\ EVAL_TAC \\ NO_TAC )
  \\ TRY ( imp_res_tac oracle_parts \\ rfs[] \\ NO_TAC)
  \\ TRY ( imp_res_tac oracle_parts_div \\ rfs[] \\ NO_TAC)
  \\ qpat_x_assum`MEM _ basis_proj2`mp_tac
  \\ simp[basis_proj2_def,basis_ffi_part_defs,cfHeapsBaseTheory.mk_proj2_def]
  \\ TRY (qpat_x_assum`_ = SOME _`mp_tac)
  \\ simp[basis_proj1_def,basis_ffi_part_defs,cfHeapsBaseTheory.mk_proj1_def,FUPDATE_LIST_THM]
  \\ rw[] \\ rw[] \\ pairarg_tac \\ fs[FLOOKUP_UPDATE] \\ rw[]
  \\ fs[FAPPLY_FUPDATE_THM,cfHeapsBaseTheory.mk_ffi_next_def]
  \\ TRY(PURE_FULL_CASE_TAC \\ fs[])
  \\ EVERY (map imp_res_tac (CONJUNCTS basis_ffi_length_thms)) \\ fs[]
  \\ srw_tac[DNF_ss][] \\ fs[ffi_exit_def]
QED

(* TODO: move somewhere else? *)
Theorem SPLIT_exists:
   (A * B) s /\ s ⊆ C
    ==> (?h1 h2. SPLIT C (h1, h2) /\ (A * B) h1)
Proof
  rw[]
  \\ qexists_tac `s` \\ qexists_tac `C DIFF s`
  \\ SPLIT_TAC
QED

val _ = export_theory();
