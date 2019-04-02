(*
  Proofs about the code in the TextIO module.
*)
open preamble
     ml_translatorTheory ml_translatorLib ml_progLib cfLib basisFunctionsLib
     mlstringTheory fsFFITheory fsFFIPropsTheory Word8ProgTheory cfMonadLib
     Word8ArrayProofTheory TextIOProgTheory MarshallingProgTheory MarshallingTheory

val _ = new_theory"TextIOProof";

val _ = translation_extends "TextIOProg";
val _ = option_monadsyntax.temp_add_option_monadsyntax();

(* heap predicate for the file-system state *)

val IOFS_iobuff_def = Define`
  IOFS_iobuff =
    SEP_EXISTS v. W8ARRAY iobuff_loc v * cond (LENGTH v >= 2052) `;

val IOFS_def = Define `
  IOFS fs = IOx (fs_ffi_part) fs * IOFS_iobuff * &wfFS fs`

Theorem UNIQUE_IOFS
`!s. VALID_HEAP s ==> !fs1 fs2 H1 H2. (IOFS fs1 * H1) s /\
                                      (IOFS fs2 * H2) s ==> fs1 = fs2`
  (rw[IOFS_def,cfHeapsBaseTheory.IOx_def, fs_ffi_part_def,
     GSYM STAR_ASSOC,encode_def] >>
  IMP_RES_TAC FRAME_UNIQUE_IO >>
  fs[IO_fs_component_equality]);

Theorem IOFS_FFI_part_hprop
  `FFI_part_hprop (IOFS fs)`
  (rw [IOFS_def,
      cfHeapsBaseTheory.IO_def, cfHeapsBaseTheory.IOx_def,
      fs_ffi_part_def, cfMainTheory.FFI_part_hprop_def,
    set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
    cfHeapsBaseTheory.W8ARRAY_def,IOFS_iobuff_def,
    cfHeapsBaseTheory.cell_def]
  \\ fs[set_sepTheory.one_STAR,STAR_def]
  \\ imp_res_tac SPLIT_SUBSET >> fs[SUBSET_DEF]
  \\ metis_tac[]);

Theorem IOFS_iobuff_HPROP_INJ[hprop_inj]
`!fs1 fs2. HPROP_INJ (IOFS fs1) (IOFS fs2) (fs2 = fs1)`
  (rw[HPROP_INJ_def, IOFS_def, GSYM STAR_ASSOC, SEP_CLAUSES, SEP_EXISTS_THM,
     HCOND_EXTRACT] >>
  fs[IOFS_def,cfHeapsBaseTheory.IOx_def, fs_ffi_part_def] >>
  EQ_TAC >> rpt DISCH_TAC >> IMP_RES_TAC FRAME_UNIQUE_IO >> fs[]);

(* "end-user" property *)
(* abstracts away the lazy list and ensure that standard streams are opened on
 * their respective standard fds at the right position *)

val STDIO_def = Define`
 STDIO fs = (SEP_EXISTS ll. IOFS (fs with numchars := ll)) *
   &STD_streams fs`

(* Used by the monadic translator *)
val MONAD_IO_def = Define `MONAD_IO fs = STDIO fs * &hasFreeFD fs`;

Theorem STDIO_numchars
  `STDIO (fs with numchars := x) = STDIO fs`
  (rw[STDIO_def,GSYM STD_streams_numchars]);

Theorem STDIO_bumpFD[simp]
  `STDIO (bumpFD fd fs n) = STDIO (forwardFD fs fd n)`
  (rw[bumpFD_forwardFD,STDIO_numchars]);

Theorem UNIQUE_STDIO
`!s. VALID_HEAP s ==> !fs1 fs2 H1 H2. (STDIO fs1 * H1) s /\
                                      (STDIO fs2 * H2) s ==>
              (fs1.infds = fs2.infds /\ fs1.files = fs2.files /\ fs1.maxFD = fs2.maxFD)`
  (rw[STDIO_def,STD_streams_def,SEP_CLAUSES,SEP_EXISTS_THM,STAR_COMM,STAR_ASSOC,cond_STAR] >>
  fs[Once STAR_COMM] >>
  imp_res_tac UNIQUE_IOFS >>
  cases_on`fs1` >> cases_on`fs2` >> fs[IO_fs_numchars_fupd]);

(* weak injection theorem *)
Theorem STDIO_HPROP_INJ[hprop_inj]
`HPROP_INJ (STDIO fs1) (STDIO fs2)
           (fs1.infds = fs2.infds /\ fs1.files = fs2.files /\ fs1.maxFD = fs2.maxFD)`
  (rw[HPROP_INJ_def, GSYM STAR_ASSOC, SEP_CLAUSES, SEP_EXISTS_THM,
     HCOND_EXTRACT] >>
  EQ_TAC >> rpt DISCH_TAC
  >-(mp_tac UNIQUE_STDIO >> disch_then drule >>
     strip_tac >>
     first_x_assum (qspecl_then [`fs1`, `fs2`] mp_tac) >>
     rpt (disch_then drule) >> fs[cond_def] >> rw[] >>
     fs[STDIO_def,STD_streams_def,STAR_def,SEP_EXISTS,cond_def] >>
     qmatch_assum_rename_tac`IOFS (fs2 with numchars := ll) u1` >>
     qmatch_assum_rename_tac`SPLIT u0 (u1, _)` >>
     qmatch_assum_rename_tac`SPLIT s (u0, v0)` >>
     qexists_tac`u0` >> qexists_tac`v0` >> fs[] >>
     qexists_tac`u1` >> fs[PULL_EXISTS] >> qexists_tac`ll` >> fs[] >>
     cases_on`fs1` >> cases_on`fs2` >> fs[IO_fs_numchars_fupd] >>
     metis_tac[]
     ) >>
  fs[STDIO_def,STD_streams_def,STAR_def,SEP_EXISTS,cond_def] >>
  qmatch_assum_rename_tac`IOFS (fs1 with numchars := ll) u1` >>
  qmatch_assum_rename_tac`SPLIT u0 (u1, _)` >>
  qmatch_assum_rename_tac`SPLIT s (u0, v0)` >>
  qexists_tac`u0` >> qexists_tac`v0` >> fs[] >>
  qexists_tac`u1` >> fs[PULL_EXISTS] >> qexists_tac`ll` >> fs[] >>
  cases_on`fs1` >> cases_on`fs2` >> fs[IO_fs_numchars_fupd] >>
  metis_tac[]);

(* refinement invariant for filenames *)

val FILENAME_def = Define `
  FILENAME s sv =
    (STRING_TYPE s sv ∧
     ¬MEM (CHR 0) (explode s) ∧
     strlen s < 256 * 256)
`;

val filename_tac = metis_tac[FILENAME_def,EqualityType_NUM_BOOL,EqualityType_def];

Theorem FILENAME_UNICITY_R[xlet_auto_match]
`!f fv fv'. FILENAME f fv ==> (FILENAME f fv' <=> fv' = fv)` (filename_tac);

Theorem FILENAME_UNICITY_L[xlet_auto_match]
`!f f' fv. FILENAME f fv ==> (FILENAME f' fv <=> f' = f)` (filename_tac);

Theorem FILENAME_STRING_UNICITY_R[xlet_auto_match]
  `!f fv fv'. FILENAME f fv ==> (STRING_TYPE f fv' <=> fv' = fv)`
  (filename_tac);

Theorem FILENAME_STRING_UNICITY_L[xlet_auto_match]
  `!f f' fv. FILENAME f fv ==> (STRING_TYPE f' fv <=> f' = f)` (filename_tac);

Theorem STRING_FILENAME_UNICITY_R[xlet_auto_match]
  `!f fv fv'. STRING_TYPE f fv ==>
    (FILENAME f fv' <=> fv' = fv /\ ¬MEM #"\^@" (explode f) /\ strlen f < 256 * 256)`
  (filename_tac);

Theorem STRING_FILENAME_UNICITY_L[xlet_auto_match]
  `!f f' fv. STRING_TYPE f fv ==>
    (FILENAME f' fv <=> f' = f /\ ¬MEM #"\^@" (explode f) /\ strlen f < 256 * 256)`
  (filename_tac);

(* exception refinement invariant lemmas *)

Theorem BadFileName_UNICITY[xlet_auto_match]
`!v1 v2. BadFileName_exn v1 ==> (BadFileName_exn v2 <=> v2 = v1)`
  (fs[BadFileName_exn_def]);

Theorem InvalidFD_UNICITY[xlet_auto_match]
`!v1 v2. InvalidFD_exn v1 ==> (InvalidFD_exn v2 <=> v2 = v1)`
  (fs[InvalidFD_exn_def]);

Theorem EndOfFile_UNICITY[xlet_auto_match]
`!v1 v2. EndOfFile_exn v1 ==> (EndOfFile_exn v2 <=> v2 = v1)`
  (fs[EndOfFile_exn_def]);

(* convenient functions for standard output/error
 * n.b. numchars is ignored *)

val stdo_def = Define`
  stdo fd name fs out =
    (ALOOKUP fs.infds fd = SOME(IOStream(strlit name),WriteMode,strlen out) /\
     ALOOKUP fs.files (IOStream(strlit name)) = SOME (explode out))`;

val _ = overload_on("stdout",``stdo 1 "stdout"``);
val _ = overload_on("stderr",``stdo 2 "stderr"``);

Theorem stdo_UNICITY_R[xlet_auto_match]
`!fd name fs out out'. stdo fd name fs out ==> (stdo fd name fs out' <=> out = out')`
(rw[stdo_def] >> EQ_TAC >> rw[explode_11]);

val up_stdo_def = Define
`up_stdo fd fs out = fsupdate fs fd 0 (strlen out) (explode out)`
val _ = overload_on("up_stdout",``up_stdo 1``);
val _ = overload_on("up_stderr",``up_stdo 2``);

Theorem stdo_numchars
  `stdo fd name (fs with numchars := l) out ⇔ stdo fd name fs out`
  (rw[stdo_def]);

Theorem up_stdo_numchars[simp]
  `(up_stdo fd fs x).numchars = fs.numchars`
  (rw[up_stdo_def,fsupdate_def]
  \\ CASE_TAC \\ CASE_TAC \\ rw[]);

Theorem up_stdo_maxFD[simp]
  `(up_stdo fd fs x).maxFD = fs.maxFD`
  (rw[up_stdo_def,fsupdate_def]
  \\ CASE_TAC \\ CASE_TAC \\ rw[]);

Theorem up_stdo_with_numchars
  `up_stdo fd (fs with numchars := ns) x =
   up_stdo fd fs x with numchars := ns`
  (rw[up_stdo_def,fsupdate_numchars]);

val add_stdo_def = Define`
  add_stdo fd nm fs out = up_stdo fd fs ((@init. stdo fd nm fs init) ^ out)`;
val _ = overload_on("add_stdout",``add_stdo 1 "stdout"``);
val _ = overload_on("add_stderr",``add_stdo 2 "stderr"``);

Theorem stdo_add_stdo
  `stdo fd nm fs init ⇒ stdo fd nm (add_stdo fd nm fs out) (strcat init out)`
  (rw[add_stdo_def]
  \\ SELECT_ELIM_TAC \\ rw[] >- metis_tac[]
  \\ imp_res_tac stdo_UNICITY_R \\ rveq
  \\ fs[up_stdo_def,stdo_def,fsupdate_def,ALIST_FUPDKEY_ALOOKUP]);

Theorem up_stdo_unchanged
 `!fs out. stdo fd nm fs out ==> up_stdo fd fs out = fs`
(fs[up_stdo_def,stdo_def,fsupdate_unchanged,get_file_content_def,PULL_EXISTS]);

Theorem stdo_up_stdo
 `!fs out out'. stdo fd nm fs out ==> stdo fd nm (up_stdo fd fs out') out'`
 (rw[up_stdo_def,stdo_def,fsupdate_def,ALIST_FUPDKEY_ALOOKUP,PULL_EXISTS]
 \\ rw[]);

Theorem add_stdo_nil
  `stdo fd nm fs out ⇒ add_stdo fd nm fs (strlit "") = fs`
  (rw[add_stdo_def]
  \\ SELECT_ELIM_TAC
  \\ metis_tac[up_stdo_unchanged]);

Theorem add_stdo_o
  `stdo fd nm fs out ⇒
   add_stdo fd nm (add_stdo fd nm fs x1) x2 = add_stdo fd nm fs (x1 ^ x2)`
  (rw[add_stdo_def]
  \\ SELECT_ELIM_TAC \\ rw[] >- metis_tac[]
  \\ SELECT_ELIM_TAC \\ rw[] >- metis_tac[stdo_up_stdo]
  \\ imp_res_tac stdo_UNICITY_R \\ rveq
  \\ rename1`stdo _ _ (up_stdo _ _ _) l`
  \\ `l = out ^ x1` by metis_tac[stdo_UNICITY_R,stdo_up_stdo]
  \\ rveq \\ fs[up_stdo_def]);

Theorem add_stdo_numchars[simp]
  `(add_stdo fd nm fs x).numchars = fs.numchars`
  (rw[add_stdo_def]);

Theorem add_stdo_maxFD[simp]
  `(add_stdo fd nm fs x).maxFD = fs.maxFD`
  (rw[add_stdo_def]);

Theorem add_stdo_with_numchars
  `add_stdo fd nm (fs with numchars := ns) x =
   add_stdo fd nm fs x with numchars := ns`
  (rw[add_stdo_def,stdo_numchars,up_stdo_with_numchars]);

Theorem up_stdo_MAP_FST_infds[simp]
  `MAP FST (up_stdo fd fs out).infds = MAP FST fs.infds`
  (rw[up_stdo_def]);

Theorem add_stdo_MAP_FST_infds[simp]
  `MAP FST (add_stdo fd nm fs out).infds = MAP FST fs.infds`
  (rw[add_stdo_def]);

Theorem up_stdo_MAP_FST_files[simp]
  `MAP FST (up_stdo fd fs out).files = MAP FST fs.files`
  (rw[up_stdo_def]);

Theorem add_stdo_MAP_FST_files[simp]
  `MAP FST (add_stdo fd nm fs out).files = MAP FST fs.files`
  (rw[add_stdo_def]);

Theorem inFS_fname_add_stdo[simp]
  `inFS_fname (add_stdo fd nm fs out) = inFS_fname fs`
  (rw[inFS_fname_def,FUN_EQ_THM]);

Theorem STD_streams_stdout
  `STD_streams fs ⇒ ∃out. stdout fs out`
  (rw[STD_streams_def,stdo_def] \\ rw[] \\ metis_tac[explode_implode,strlen_implode]);

Theorem STD_streams_stderr
  `STD_streams fs ⇒ ∃out. stderr fs out`
  (rw[STD_streams_def,stdo_def] \\ rw[] \\ metis_tac[explode_implode,strlen_implode]);

Theorem STD_streams_add_stdout
  `STD_streams fs ⇒ STD_streams (add_stdout fs out)`
  (rw[]
  \\ imp_res_tac STD_streams_stdout
  \\ rw[add_stdo_def]
  \\ SELECT_ELIM_TAC
  \\ rw[] >- metis_tac[]
  \\ rw[up_stdo_def]
  \\ match_mp_tac STD_streams_fsupdate \\ rw[]);

Theorem STD_streams_add_stderr
  `STD_streams fs ⇒ STD_streams (add_stderr fs out)`
  (rw[]
  \\ imp_res_tac STD_streams_stderr
  \\ rw[add_stdo_def]
  \\ SELECT_ELIM_TAC
  \\ rw[] >- metis_tac[]
  \\ rw[up_stdo_def]
  \\ match_mp_tac STD_streams_fsupdate \\ rw[]);

Theorem validFD_up_stdo[simp]
  `validFD fd (up_stdo fd' fs out) ⇔ validFD fd fs`
  (rw[up_stdo_def]);

Theorem validFD_add_stdo[simp]
  `validFD fd (add_stdo fd' nm fs out) ⇔ validFD fd fs`
  (rw[add_stdo_def]);

Theorem validFileFD_up_stdo[simp]
  `validFileFD fd (up_stdo fd' fs out).infds ⇔ validFileFD fd fs.infds`
  (rw[up_stdo_def]);

Theorem validFileFD_add_stdo[simp]
  `validFileFD fd (add_stdo fd' nm fs out).infds ⇔ validFileFD fd fs.infds`
  (rw[add_stdo_def]);

Theorem up_stdo_A_DELKEY
  `fd ≠ fd' ⇒
   up_stdo fd (fs with infds updated_by A_DELKEY fd') out =
   up_stdo fd fs out with infds updated_by A_DELKEY fd'`
  (rw[up_stdo_def,fsupdate_A_DELKEY]);

Theorem stdo_A_DELKEY
  `fd ≠ fd' ⇒
   stdo fd nm (fs with infds updated_by A_DELKEY fd') = stdo fd nm fs`
  (rw[stdo_def,FUN_EQ_THM,ALOOKUP_ADELKEY]);

Theorem add_stdo_A_DELKEY
  `fd ≠ fd' ⇒
   add_stdo fd nm (fs with infds updated_by A_DELKEY fd') out =
   add_stdo fd nm fs out with infds updated_by A_DELKEY fd'`
  (rw[add_stdo_def,up_stdo_A_DELKEY,stdo_A_DELKEY]);

Theorem get_file_content_add_stdout
  `STD_streams fs ∧ fd ≠ 1 ⇒
   get_file_content (add_stdout fs out) fd = get_file_content fs fd`
  (rw[get_file_content_def,add_stdo_def,up_stdo_def,fsupdate_def]
  \\ CASE_TAC \\ CASE_TAC \\ simp[ALIST_FUPDKEY_ALOOKUP]
  \\ TOP_CASE_TAC \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ CASE_TAC
  >- metis_tac[STD_streams_def,SOME_11,PAIR,FST,SND]
  \\ CASE_TAC);

Theorem get_mode_add_stdo[simp]
  `get_mode (add_stdo fd nm fs x) fd' = get_mode fs fd'`
  (rw[get_mode_def,add_stdo_def, up_stdo_def, fsupdate_def]
  \\ TOP_CASE_TAC \\ rw[]
  \\ TOP_CASE_TAC \\ rw[]
  \\ simp[ALIST_FUPDKEY_ALOOKUP]
  \\ TOP_CASE_TAC \\ rw[]);

Theorem get_mode_bumpFD[simp]
  `get_mode (bumpFD fd fs n) fd' = get_mode fs fd'`
  (rw[get_mode_def,bumpFD_def,ALIST_FUPDKEY_ALOOKUP]
  \\ TOP_CASE_TAC \\ rw[]);

Theorem linesFD_add_stdout
  `STD_streams fs ∧ fd ≠ 1 ⇒
   linesFD (add_stdout fs out) fd = linesFD fs fd`
  (rw[linesFD_def,get_file_content_add_stdout]);

Theorem get_file_content_add_stderr
  `STD_streams fs ∧ fd ≠ 2 ⇒
   get_file_content (add_stderr fs err) fd = get_file_content fs fd`
  (rw[get_file_content_def,add_stdo_def,up_stdo_def,fsupdate_def]
  \\ CASE_TAC \\ CASE_TAC \\ simp[ALIST_FUPDKEY_ALOOKUP]
  \\ TOP_CASE_TAC \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ CASE_TAC
  >- metis_tac[STD_streams_def,SOME_11,PAIR,FST,SND]
  \\ CASE_TAC);

Theorem linesFD_add_stderr
  `STD_streams fs ∧ fd ≠ 2 ⇒
   linesFD (add_stderr fs err) fd = linesFD fs fd`
  (rw[linesFD_def,get_file_content_add_stderr]);

Theorem up_stdo_forwardFD
  `fd ≠ fd' ⇒ up_stdo fd' (forwardFD fs fd n) out = forwardFD (up_stdo fd' fs out) fd n`
  (rw[forwardFD_def,up_stdo_def,fsupdate_def,ALIST_FUPDKEY_ALOOKUP]
  \\ CASE_TAC \\ CASE_TAC \\ rw[]
  \\ rpt(AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ match_mp_tac ALIST_FUPDKEY_comm \\ rw[]);

Theorem up_stdout_fastForwardFD
  `STD_streams fs ⇒
   up_stdout (fastForwardFD fs fd) out = fastForwardFD (up_stdout fs out) fd`
  (rw[fastForwardFD_def,up_stdo_def]
  \\ Cases_on`ALOOKUP fs.infds fd` >- (
    fs[libTheory.the_def,fsupdate_def]
    \\ CASE_TAC \\ fs[libTheory.the_def]
    \\ CASE_TAC \\ fs[libTheory.the_def,ALIST_FUPDKEY_ALOOKUP] )
  \\ fs[] \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.files fnm` >- (
    fs[libTheory.the_def,fsupdate_def]
    \\ CASE_TAC \\ fs[libTheory.the_def]
    \\ CASE_TAC \\ fs[libTheory.the_def,ALIST_FUPDKEY_ALOOKUP]
    \\ rw[libTheory.the_def] )
  \\ fs[libTheory.the_def]
  \\ fs[fsupdate_def,libTheory.the_def,ALIST_FUPDKEY_ALOOKUP]
  \\ CASE_TAC \\ fs[libTheory.the_def,ALIST_FUPDKEY_ALOOKUP]
  >- ( rw[ALIST_FUPDKEY_o,o_DEF,PAIR_MAP] )
  \\ CASE_TAC \\ fs[libTheory.the_def]
  \\ CASE_TAC \\ fs[libTheory.the_def,ALIST_FUPDKEY_ALOOKUP]
  \\ rw[libTheory.the_def,ALIST_FUPDKEY_comm]
  \\ metis_tac[STD_streams_def,SOME_11,PAIR,FST,SND]);

Theorem up_stderr_fastForwardFD
  `STD_streams fs ⇒
   up_stderr (fastForwardFD fs fd) out = fastForwardFD (up_stderr fs out) fd`
  (rw[fastForwardFD_def,up_stdo_def]
  \\ Cases_on`ALOOKUP fs.infds fd` >- (
    fs[libTheory.the_def,fsupdate_def]
    \\ CASE_TAC \\ fs[libTheory.the_def]
    \\ CASE_TAC \\ fs[libTheory.the_def,ALIST_FUPDKEY_ALOOKUP] )
  \\ fs[] \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.files fnm` >- (
    fs[libTheory.the_def,fsupdate_def]
    \\ CASE_TAC \\ fs[libTheory.the_def]
    \\ CASE_TAC \\ fs[libTheory.the_def,ALIST_FUPDKEY_ALOOKUP]
    \\ rw[libTheory.the_def] )
  \\ fs[libTheory.the_def]
  \\ fs[fsupdate_def,libTheory.the_def,ALIST_FUPDKEY_ALOOKUP]
  \\ CASE_TAC \\ fs[libTheory.the_def,ALIST_FUPDKEY_ALOOKUP]
  >- ( rw[ALIST_FUPDKEY_o,o_DEF,PAIR_MAP] )
  \\ CASE_TAC \\ fs[libTheory.the_def]
  \\ CASE_TAC \\ fs[libTheory.the_def,ALIST_FUPDKEY_ALOOKUP]
  \\ rw[libTheory.the_def,ALIST_FUPDKEY_comm]
  \\ metis_tac[STD_streams_def,SOME_11,PAIR,FST,SND]);

Theorem stdo_forwardFD
  `fd ≠ fd' ⇒ (stdo fd' nm (forwardFD fs fd n) out ⇔ stdo fd' nm fs out)`
  (rw[stdo_def,forwardFD_def,ALIST_FUPDKEY_ALOOKUP]
  \\ CASE_TAC);

Theorem stdo_fastForwardFD
  `fd ≠ fd' ⇒ (stdo fd' nm (fastForwardFD fs fd) out ⇔ stdo fd' nm fs out)`
  (rw[stdo_def,fastForwardFD_def,ALIST_FUPDKEY_ALOOKUP]
  \\ Cases_on`ALOOKUP fs.infds fd` \\ fs[libTheory.the_def]
  \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.files fnm` \\ fs[libTheory.the_def]
  \\ fs[ALIST_FUPDKEY_ALOOKUP] \\ rw[]
  \\ CASE_TAC);

Theorem add_stdo_forwardFD
  `fd ≠ fd' ⇒ add_stdo fd' nm (forwardFD fs fd n) out = forwardFD (add_stdo fd' nm fs out) fd n`
  (rw[add_stdo_def,stdo_forwardFD,up_stdo_forwardFD]);

Theorem add_stdout_lineForwardFD
  `STD_streams fs ∧ fd ≠ 1 ⇒
   add_stdout (lineForwardFD fs fd) out = lineForwardFD (add_stdout fs out) fd`
  (rw[lineForwardFD_def,get_file_content_add_stdout]
  \\ CASE_TAC \\ CASE_TAC
  \\ rw[] \\ pairarg_tac \\ fs[add_stdo_forwardFD]);

Theorem add_stdout_fastForwardFD
  `STD_streams fs ∧ fd ≠ 1 ⇒
   add_stdout (fastForwardFD fs fd) out = fastForwardFD (add_stdout fs out) fd`
  (rw[add_stdo_def,up_stdout_fastForwardFD,stdo_fastForwardFD]);

Theorem add_stderr_lineForwardFD
  `STD_streams fs ∧ fd ≠ 2 ⇒
   add_stderr (lineForwardFD fs fd) out = lineForwardFD (add_stderr fs out) fd`
  (rw[lineForwardFD_def,get_file_content_add_stderr]
  \\ CASE_TAC \\ CASE_TAC
  \\ rw[] \\ pairarg_tac \\ fs[add_stdo_forwardFD]);

Theorem add_stderr_fastForwardFD
  `STD_streams fs ∧ fd ≠ 2 ⇒
   add_stderr (fastForwardFD fs fd) out = fastForwardFD (add_stderr fs out) fd`
  (rw[add_stdo_def,up_stderr_fastForwardFD,stdo_fastForwardFD]);

Theorem FILTER_File_add_stdo
  `stdo fd nm fs init ⇒
   FILTER (isFile o FST) (add_stdo fd nm fs out).files = FILTER (isFile o FST) fs.files`
  (rw[add_stdo_def,up_stdo_def,fsupdate_def]
  \\ CASE_TAC \\ CASE_TAC \\ fs[]
  \\ match_mp_tac FILTER_EL_EQ \\ simp[]
  \\ qmatch_assum_rename_tac`_ = SOME (k,_)`
  \\ qx_gen_tac`n`
  \\ simp[GSYM AND_IMP_INTRO] \\ strip_tac
  \\ reverse(Cases_on`FST (EL n fs.files) = k`)
  >- simp[EL_ALIST_FUPDKEY_unchanged]
  \\ simp[FST_EL_ALIST_FUPDKEY,GSYM AND_IMP_INTRO]
  \\ fs[stdo_def]);

Theorem FILTER_File_add_stdout
  `STD_streams fs ⇒
   FILTER (isFile o FST) (add_stdout fs out).files = FILTER (isFile o FST) fs.files`
  (metis_tac[STD_streams_stdout,FILTER_File_add_stdo]);

Theorem FILTER_File_add_stderr
  `STD_streams fs ⇒
   FILTER (isFile o FST) (add_stderr fs out).files = FILTER (isFile o FST) fs.files`
  (metis_tac[STD_streams_stderr,FILTER_File_add_stdo]);

val stdin_def = Define
`stdin fs inp pos = (ALOOKUP fs.infds 0 = SOME(IOStream(strlit"stdin"),ReadMode,pos) /\
                     ALOOKUP fs.files (IOStream(strlit"stdin"))= SOME inp)`

val up_stdin_def = Define
`up_stdin inp pos fs = fsupdate fs 0 0 pos inp`

val get_stdin_def = Define`
  get_stdin fs = let (inp,pos) = @(inp,pos). stdin fs inp pos in DROP pos inp`;

Theorem stdin_11
  `stdin fs i1 p1 ∧ stdin fs i2 p2 ⇒ i1 = i2 ∧ p1 = p2`
  (rw[stdin_def] \\ fs[]);

Theorem stdin_get_file_content
  `stdin fs inp pos ⇒ get_file_content fs 0 = SOME (inp,pos)`
  (rw[stdin_def,fsFFITheory.get_file_content_def]);

Theorem stdin_forwardFD
  `stdin fs inp pos ⇒
   stdin (forwardFD fs fd n) inp (if fd = 0 then pos+n else pos)`
  (rw[stdin_def,forwardFD_def]
  \\ simp[ALIST_FUPDKEY_ALOOKUP]);

Theorem stdin_get_stdin
  `stdin fs inp pos ⇒ get_stdin fs = DROP pos inp`
  (rw[get_stdin_def]
  \\ SELECT_ELIM_TAC
  \\ rw[EXISTS_PROD,FORALL_PROD]
  >- metis_tac[]
  \\ pairarg_tac \\ fs[]
  \\ imp_res_tac stdin_11 \\ fs[]);

Theorem get_stdin_forwardFD
  `stdin fs inp pos ⇒
   get_stdin (forwardFD fs fd n) =
   if fd = 0 then
     DROP n (get_stdin fs)
   else get_stdin fs`
  (strip_tac
  \\ imp_res_tac stdin_get_stdin
  \\ imp_res_tac stdin_forwardFD
  \\ first_x_assum(qspecl_then[`n`,`fd`]mp_tac)
  \\ strip_tac
  \\ simp[DROP_DROP_T]
  \\ imp_res_tac stdin_get_stdin
  \\ rw[]);

Theorem linesFD_splitlines_get_stdin
  `stdin fs inp pos ⇒
   MAP (λl. l ++ "\n") (splitlines (get_stdin fs)) = linesFD fs 0`
  (rw[linesFD_def]
  \\ imp_res_tac stdin_get_stdin
  \\ fs[stdin_def,get_file_content_def]);

(* file descriptors are encoded on 8 bytes *)
val FD_def = Define `
  FD fd fdv = (STRING_TYPE (strlit(MAP (CHR ∘ w2n) (n2w8 fd))) fdv ∧ fd < 256**8)`;

val INSTREAM_def = Define `
  INSTREAM fd fdv <=>
    INSTREAM_TYPE (Instream (strlit(MAP (CHR ∘ w2n) (n2w8 fd)))) fdv ∧
    fd < 256**8`

val OUTSTREAM_def = Define `
  OUTSTREAM fd fdv <=>
    OUTSTREAM_TYPE (Outstream (strlit(MAP (CHR ∘ w2n) (n2w8 fd)))) fdv ∧
    fd < 256**8`

Theorem INSTREAM_stdin
  `INSTREAM 0 stdin_v`
  (fs[INSTREAM_def,MarshallingTheory.n2w8_def,stdin_v_thm,GSYM stdIn_def]);

Theorem OUTSTREAM_stdout
  `OUTSTREAM 1 stdout_v`
  (fs[OUTSTREAM_def,MarshallingTheory.n2w8_def,stdout_v_thm,GSYM stdOut_def]);

Theorem OUTSTREAM_stderr
  `OUTSTREAM 2 stderr_v`
  (fs[OUTSTREAM_def,MarshallingTheory.n2w8_def,stderr_v_thm,GSYM stdErr_def]);

(* -- *)

Theorem openIn_spec
  `∀s sv fs.
     FILENAME s sv ∧
     hasFreeFD fs ⇒
     app (p:'ffi ffi_proj) TextIO_openIn_v [sv]
       (IOFS fs)
       (POSTve
          (\fdv. &(INSTREAM (nextFD fs) fdv ∧
                  validFD (nextFD fs) (openFileFS s fs ReadMode 0) ∧
                  inFS_fname fs (File s)) *
                IOFS (openFileFS s fs ReadMode 0))
          (\e. &(BadFileName_exn e ∧ ~inFS_fname fs (File s)) * IOFS fs))`
  (rw [] >> qpat_abbrev_tac `Q = POSTve _ _` >>
  simp [IOFS_def, fs_ffi_part_def, IOx_def, IO_def] >>
  xpull >> qunabbrev_tac `Q` >>
  xcf_with_def "TextIO.openIn" TextIO_openIn_v_def >>
  fs[FILENAME_def, strlen_def, IOFS_def, IOFS_iobuff_def] >>
  xpull >> rename [`W8ARRAY _ fnm0`] >>
  qmatch_goalsub_abbrev_tac`catfs fs * _` >>
  rpt(xlet_auto >- xsimpl) >>
  qmatch_goalsub_abbrev_tac`W8ARRAY _ fd0` >>
  qmatch_goalsub_rename_tac`W8ARRAY loc fd0` >>
  qmatch_goalsub_abbrev_tac`catfs fs' * _` >>
  Cases_on `inFS_fname fs (File s)`
  >- (xlet `POSTv u2.
            &(UNIT_TYPE () u2 /\ nextFD fs < fs.maxFD /\
              validFD (nextFD fs) (openFileFS s fs ReadMode 0)) *
            W8ARRAY loc (0w :: n2w8(nextFD fs)) *
            W8ARRAY iobuff_loc fnm0 *
            catfs fs'`
    >- (simp[Abbr`catfs`,Abbr`fs'`] >>
        xffi >> xsimpl >>
        qexists_tac`(MAP (n2w o ORD) (explode s) ++ [0w])` >>
        fs[strcat_thm,implode_def] >>
        simp[fsFFITheory.fs_ffi_part_def,IOx_def,IO_def] >>
        qmatch_goalsub_abbrev_tac `FFI_part st f ns` >>
        CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac[`events`,`ns`,`f`,`st`]
        >> xsimpl >>
        simp[Abbr`f`,Abbr`st`,Abbr`ns`, mk_ffi_next_def,
             ffi_open_in_def, (* decode_encode_FS, *) Abbr`fd0`,
             getNullTermStr_add_null, MEM_MAP, ORD_BOUND, ORD_eq_0,
             dimword_8, MAP_MAP_o, o_DEF, char_BIJ,str_def,strcat_thm,
             LENGTH_explode,REPLICATE_compute,LUPDATE_compute,explode_implode] >>
        `∃content. ALOOKUP fs.files (File s) = SOME content`
          by (fs[inFS_fname_def, ALOOKUP_EXISTS_IFF, MEM_MAP, EXISTS_PROD] >>
              metis_tac[]) >>
             (* fs[DROP_LENGTH_TOO_LONG,LENGTH_REPLICATE] *)
        imp_res_tac nextFD_ltX >>
        csimp[openFileFS_def, openFile_def, validFD_def] >>
        fs[STRING_TYPE_def] \\ xsimpl >>
        qpat_abbrev_tac `new_events = events ++ _` >>
        qexists_tac `new_events` >> xsimpl) >>
    xlet_auto >- xsimpl >>
    xlet_auto >- xsimpl >>
    xlet_auto >- (xsimpl >> imp_res_tac WORD_UNICITY_R >> fs[])
    >> xif >>
    instantiate >>
    xlet_auto >- (xsimpl \\ fs [LENGTH_n2w8]) >>
    reverse xcon >- xsimpl >>
    simp[INSTREAM_def] >> xsimpl >> fs [INSTREAM_TYPE_def] >>
    fs[EL_LUPDATE,Abbr`fd0`,LENGTH_explode,LENGTH_n2w8,TAKE_LENGTH_ID_rwt] >>
    imp_res_tac nextFD_ltX >>
    fs[wfFS_openFile,Abbr`fs'`,liveFS_openFileFS]) >>
  xlet `POSTv u2.
            &UNIT_TYPE () u2 * catfs fs * W8ARRAY iobuff_loc fnm0 *
            W8ARRAY loc (LUPDATE 1w 0 fd0)`
  >- (simp[Abbr`catfs`,Abbr`fs'`] >> xffi >> xsimpl >>
      simp[fsFFITheory.fs_ffi_part_def,IOx_def,IO_def] >>
      qmatch_goalsub_abbrev_tac `FFI_part st f ns` >>
      CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
      map_every qexists_tac[`events`,`ns`,`f`,`st`] >> xsimpl >>
      qexists_tac`(MAP (n2w o ORD) (explode s) ++ [0w])` >>
      fs[strcat_thm,implode_def] >>
      simp[Abbr`f`,Abbr`st`,Abbr`ns`, mk_ffi_next_def,
           ffi_open_in_def, (* decode_encode_FS, *) Abbr`fd0`,
           getNullTermStr_add_null, MEM_MAP, ORD_BOUND, ORD_eq_0,
           dimword_8, MAP_MAP_o, o_DEF, char_BIJ,str_def,strcat_thm,
           implode_explode, LENGTH_explode] >>
      fs[not_inFS_fname_openFile,STRING_TYPE_def] \\ xsimpl >>
      qpat_abbrev_tac `new_events = events ++ _` >>
      qexists_tac `new_events` >> xsimpl) >>
  xlet_auto >-(xsimpl) >> fs[] >>
  xlet_auto >- xsimpl >>
  xlet_auto >- (xsimpl >> imp_res_tac WORD_UNICITY_R) >>
  xif >-(rfs[Abbr`fd0`,EL_LUPDATE,HD_LUPDATE]) >>
  xlet_auto >-(xcon >> xsimpl) >> xraise >> xsimpl >>
  simp[BadFileName_exn_def,Abbr`fd0`,LENGTH_explode]);

(* STDIO version *)
Theorem openIn_STDIO_spec
  `∀s sv fs.
     FILENAME s sv ∧
     hasFreeFD fs ⇒
     app (p:'ffi ffi_proj) TextIO_openIn_v [sv]
       (STDIO fs)
       (POSTve
          (\fdv. &(INSTREAM (nextFD fs) fdv ∧
                  validFD (nextFD fs) (openFileFS s fs ReadMode 0) ∧
                  inFS_fname fs (File s)) *
                STDIO (openFileFS s fs ReadMode 0))
          (\e. &(BadFileName_exn e ∧ ~inFS_fname fs (File s)) * STDIO fs))`
 (rw[STDIO_def] >> xpull >> xapp_spec openIn_spec >>
 map_every qexists_tac [`emp`,`s`,`fs with numchars := ll`] >>
 xsimpl >> rw[] >> qexists_tac`ll` >> fs[openFileFS_fupd_numchars] >> xsimpl >>
 rw[] >>
 fs[nextFD_numchars,nextFD_numchars,openFileFS_fupd_numchars,STD_streams_openFileFS] >>
 fs[GSYM validFD_numchars,GSYM openFileFS_fupd_numchars,inFS_fname_numchars])

(* openOut, openAppend here *)

Theorem closeIn_spec
  `∀fdw fdv fs.
     INSTREAM fdw fdv ⇒
     app (p:'ffi ffi_proj) TextIO_closeIn_v [fdv]
       (IOFS fs)
       (POSTve
          (\u. &(UNIT_TYPE () u /\ validFileFD fdw fs.infds) *
               IOFS (fs with infds updated_by A_DELKEY fdw))
          (\e. &(InvalidFD_exn e /\ ¬ validFileFD fdw fs.infds) * IOFS fs))`
  (rw [] >> qpat_abbrev_tac `Q = POSTve _ _` >>
  simp [IOFS_def, fs_ffi_part_def, IOx_def, IO_def] >>
  xpull >> qunabbrev_tac `Q` >>
  xcf_with_def "TextIO.closeIn" TextIO_closeIn_v_def >>
  fs[IOFS_def, IOFS_iobuff_def,INSTREAM_def] >> xpull >>
  rename [`W8ARRAY _ buf`] >> cases_on`buf` >> fs[LUPDATE_def] >>
  xlet_auto >- xsimpl >> fs [get_in_def] >>
  xlet`POSTv uv. &(UNIT_TYPE () uv) *
        W8ARRAY iobuff_loc ((if validFileFD fdw fs.infds then 0w else 1w) ::t) *
        IOx fs_ffi_part (if validFileFD fdw fs.infds then
                            (fs with infds updated_by A_DELKEY fdw)
                         else fs)`
  >-(xffi >> simp[IOFS_def,fsFFITheory.fs_ffi_part_def,IOx_def,IO_def] >>
     qmatch_goalsub_abbrev_tac`FFI_part st f ns` >> xsimpl >>
     qmatch_goalsub_abbrev_tac`FFI_part (_ fs') f ns` >>
     CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
     map_every qexists_tac[`events`,`ns`,`f`,`st`] >> xsimpl >>
     qexists_tac`n2w8 fdw` >> fs[FD_def] >>
     unabbrev_all_tac >>
     simp[validFileFD_def] >>
     Cases_on`ALOOKUP fs.infds fdw` \\ fs[] \\
     TRY(PairCases_on`x`) \\
     fs[mk_ffi_next_def, ffi_close_def, (* decode_encode_FS, *)
        getNullTermStr_insert_atI, ORD_BOUND, ORD_eq_0,option_eq_some,
        dimword_8, MAP_MAP_o, o_DEF, char_BIJ,w82n_n2w8,LENGTH_n2w8,
        implode_explode, LENGTH_explode,closeFD_def,LUPDATE_def] >>
     cases_on`fs` >> fs[IO_fs_infds_fupd] >>
     imp_res_tac ALOOKUP_NONE >> rw[] \\
     fs[liveFS_def,IO_fs_infds_fupd,STRING_TYPE_def] \\ xsimpl >>
     qpat_abbrev_tac `new_events = events ++ _` >>
     qexists_tac `new_events` >> xsimpl) >>
  NTAC 3 (xlet_auto >- xsimpl) >>
  CASE_TAC >> xif >> instantiate
  >-(xcon >> fs[IOFS_def,liveFS_def] >> xsimpl) >>
  xlet_auto >-(xcon >> xsimpl) >>
  xraise >> fs[InvalidFD_exn_def,IOFS_def] >> xsimpl);

Theorem closeOut_spec
  `∀fdw fdv fs.
     OUTSTREAM fdw fdv ⇒
     app (p:'ffi ffi_proj) TextIO_closeOut_v [fdv]
       (IOFS fs)
       (POSTve
         (\u. &(UNIT_TYPE () u /\ validFileFD fdw fs.infds) *
              IOFS (fs with infds updated_by A_DELKEY fdw))
         (\e. &(InvalidFD_exn e /\ ¬ validFileFD fdw fs.infds) * IOFS fs))`
  (rw [] >> qpat_abbrev_tac `Q = POSTve _ _` >>
  simp [IOFS_def, fs_ffi_part_def, IOx_def, IO_def] >>
  xpull >> qunabbrev_tac `Q` >>
  xcf_with_def "TextIO.closeOut" TextIO_closeOut_v_def >>
  fs[IOFS_def, IOFS_iobuff_def,OUTSTREAM_def] >> xpull >>
  rename [`W8ARRAY _ buf`] >> cases_on`buf` >> fs[LUPDATE_def] >>
  xlet_auto >- xsimpl >> fs [get_out_def] >>
  xlet`POSTv uv. &(UNIT_TYPE () uv) *
        W8ARRAY iobuff_loc ((if validFileFD fdw fs.infds then 0w else 1w) ::t) *
        IOx fs_ffi_part (if validFileFD fdw fs.infds then
                            (fs with infds updated_by A_DELKEY fdw)
                         else fs)`
  >-(xffi >> simp[IOFS_def,fsFFITheory.fs_ffi_part_def,IOx_def,IO_def] >>
     qmatch_goalsub_abbrev_tac `FFI_part st f ns` >> xsimpl >>
     qmatch_goalsub_abbrev_tac `FFI_part (_ fs') f ns` >>
     CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
     map_every qexists_tac[`events`,`ns`,`f`,`st`] >> xsimpl >>
     qexists_tac`n2w8 fdw` >> fs[FD_def] >>
     unabbrev_all_tac >>
     simp[validFileFD_def] >>
     Cases_on`ALOOKUP fs.infds fdw` \\ fs[] \\
     TRY(PairCases_on`x`) \\
     fs[mk_ffi_next_def, ffi_close_def, (* decode_encode_FS, *)
        getNullTermStr_insert_atI, ORD_BOUND, ORD_eq_0,option_eq_some,
        dimword_8, MAP_MAP_o, o_DEF, char_BIJ,w82n_n2w8,LENGTH_n2w8,
        implode_explode, LENGTH_explode,closeFD_def,LUPDATE_def] >>
     cases_on`fs` >> fs[IO_fs_infds_fupd] >>
     imp_res_tac ALOOKUP_NONE >> rw[] \\
     fs[liveFS_def,IO_fs_infds_fupd,STRING_TYPE_def] \\ xsimpl >>
     qpat_abbrev_tac `new_events = events ++ _` >>
     qexists_tac `new_events` >> xsimpl) >>
  NTAC 3 (xlet_auto >- xsimpl) >>
  CASE_TAC >> xif >> instantiate
  >-(xcon >> fs[IOFS_def,liveFS_def] >> xsimpl) >>
  xlet_auto >-(xcon >> xsimpl) >>
  xraise >> fs[InvalidFD_exn_def,IOFS_def] >> xsimpl);

Theorem closeIn_STDIO_spec
  `∀fd fs fdv.
     INSTREAM fd fdv /\ fd >= 3 /\ fd <= fs.maxFD ⇒
     app (p:'ffi ffi_proj) TextIO_closeIn_v [fdv]
       (STDIO fs)
       (POSTve
          (\u. &(UNIT_TYPE () u /\ validFileFD fd fs.infds) *
               STDIO (fs with infds updated_by A_DELKEY fd))
          (\e. &(InvalidFD_exn e /\ ¬ validFileFD fd fs.infds) * STDIO fs))`
  (rw[STDIO_def] >> xpull >> xapp_spec closeIn_spec >>
  map_every qexists_tac [`emp`,`fs with numchars := ll`,`fd`] >>
  xsimpl >> rw[] >> qexists_tac`ll` >> fs[validFileFD_def] >> xsimpl >>
  fs[STD_streams_def,ALOOKUP_ADELKEY] \\
  Cases_on`fd = 0` \\ fs[]
  \\ Cases_on`fd = 1` \\ fs[]
  \\ Cases_on`fd = 2` \\ fs[]
  \\ metis_tac[]);

Theorem closeOut_STDIO_spec
  `∀fd fs fdv.
     OUTSTREAM fd fdv /\ fd >= 3 /\ fd <= fs.maxFD ⇒
     app (p:'ffi ffi_proj) TextIO_closeOut_v [fdv]
       (STDIO fs)
       (POSTve
          (\u. &(UNIT_TYPE () u /\ validFileFD fd fs.infds) *
               STDIO (fs with infds updated_by A_DELKEY fd))
          (\e. &(InvalidFD_exn e /\ ¬ validFileFD fd fs.infds) * STDIO fs))`
  (rw[STDIO_def] >> xpull >> xapp_spec closeOut_spec >>
  map_every qexists_tac [`emp`,`fs with numchars := ll`,`fd`] >>
  xsimpl >> rw[] >> qexists_tac`ll` >> fs[validFileFD_def] >> xsimpl >>
  fs[STD_streams_def,ALOOKUP_ADELKEY] \\
  Cases_on`fd = 0` \\ fs[]
  \\ Cases_on`fd = 1` \\ fs[]
  \\ Cases_on`fd = 2` \\ fs[]
  \\ metis_tac[]);

Theorem writei_spec
 `wfFS fs ⇒ 0 < n ⇒
   MAX (i+n) 2048 <= LENGTH rest ⇒ i + n < 256**2 ⇒
  get_file_content fs fd = SOME(content, pos) ⇒
  get_mode fs fd = SOME WriteMode ⇒
  FD fd fdv ⇒ NUM n nv ⇒ NUM i iv ⇒
  bc = h1 :: h2 :: h3 :: h4 :: rest ⇒
  app (p:'ffi ffi_proj) TextIO_writei_v [fdv;nv;iv]
  (IOx fs_ffi_part fs * W8ARRAY iobuff_loc bc)
  (POSTve
    (\nwv. SEP_EXISTS nw. &(NUM nw nwv) * &(nw > 0) * &(nw <= n) *
           W8ARRAY iobuff_loc (0w :: n2w2 nw ++ (n2w i :: rest)) *
           IOx fs_ffi_part
               (fsupdate fs fd (1 + Lnext_pos fs.numchars) (pos + nw)
                  (insert_atI (TAKE nw (MAP (CHR o w2n) (DROP i rest))) pos
                                    content)))
    (\e. &(InvalidFD_exn e) * W8ARRAY iobuff_loc (1w :: n2w n :: n2w2 i ++ rest) * &(F) *
         IOFS (fs with numchars:= THE(LDROP (1 + Lnext_pos fs.numchars) fs.numchars))))`
  (strip_tac >>
  `?ll. fs.numchars = ll` by simp[]  >> fs[] >>
  `ll ≠ [||]`  by (cases_on`ll` >> fs[wfFS_def,liveFS_def,live_numchars_def]) >>
  `always (eventually (λll. ∃k. LHD ll = SOME k ∧ k ≠ 0)) ll`
    by fs[wfFS_def,liveFS_def,live_numchars_def] >>
  reverse(Cases_on`validFD fd fs`) >- metis_tac[get_file_content_validFD] \\
  pop_assum mp_tac \\
  UNDISCH_TAC ``fs.numchars = ll`` >> LAST_X_ASSUM MP_TAC >>
  LAST_ASSUM MP_TAC >>
  map_every qid_spec_tac [`bc`, `h4`, `h3`, `h2`, `h1`, `fs`] >>
  NTAC 2 (FIRST_X_ASSUM MP_TAC) >> qid_spec_tac `ll` >>
  HO_MATCH_MP_TAC always_eventually_ind >>
  xcf_with_def "TextIO.writei" TextIO_writei_v_def >> fs[FD_def]
(* next el is <> 0 *)
  >-(sg`Lnext_pos ll = 0`
     >-(fs[Lnext_pos_def,Once Lnext_def,liveFS_def,live_numchars_def,always_thm] >>
        cases_on`ll` >> fs[]) >>
     NTAC 2 ((xlet_auto >> fs[n2w2_def,insert_atI_def]) >- xsimpl) >>
     xlet`POSTv uv. &(UNIT_TYPE () uv) *
            W8ARRAY iobuff_loc ((0w :: n2w (MIN n k DIV 256)::n2w (MIN n k) :: n2w i :: rest)) *
            IOx fs_ffi_part (fsupdate fs fd 1 (MIN n k + pos)
                          (TAKE pos content ++
                           TAKE (MIN n k) (MAP (CHR o w2n) (DROP i rest)) ++
                           DROP (MIN n k + pos) content))`
     >-(qmatch_goalsub_abbrev_tac` _ * _ * IOx _ fs'` >>
        qpat_abbrev_tac `Q = $POSTv _` >>
        simp [fs_ffi_part_def, IOx_def, IO_def] >>
        xpull >> qunabbrev_tac `Q` >>
        xffi >> xsimpl >>
        fs[IOFS_def,IOx_def,fs_ffi_part_def,
               mk_ffi_next_def, IO_def] >>
        qmatch_goalsub_abbrev_tac `FFI_part st f ns` >>
        CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac[`events`,`ns`,`f`,`st`] >> xsimpl >>
        qexists_tac`n2w8 fd` >>
        fs[Abbr`f`,Abbr`st`,Abbr`ns`,mk_ffi_next_def,w82n_n2w8,LENGTH_n2w8,
           ffi_write_def,(* decode_encode_FS, *)MEM_MAP, ORD_BOUND,ORD_eq_0,wfFS_LDROP,
           dimword_8, MAP_MAP_o,o_DEF,char_BIJ,implode_explode,LENGTH_explode,
           HD_LUPDATE,LUPDATE_def,option_eq_some,validFD_def,write_def,
           get_file_content_def] >>
        pairarg_tac >> fs[] >> xsimpl >>
        `MEM fd (MAP FST fs.infds)` by (metis_tac[MEM_MAP]) >>
        rw[] >> TRY(metis_tac[STRING_TYPE_def,wfFS_fsupdate,liveFS_fsupdate]) >>
        cases_on`fs.numchars` >> fs[Abbr`fs'`,fsupdate_def] >>
        fs[GSYM n2w2_def] >>
        `i < 2 ** (2 * 8)` by fs[] >> imp_res_tac w22n_n2w2 >>
        `n < 2 ** (2 * 8)` by fs[] >> imp_res_tac w22n_n2w2 >>
        rw[] >> rfs[]
        \\ Cases_on`md` \\ fs[]
        >- rfs[get_mode_def]
        \\ xsimpl \\ simp[n2w2_def] >>
        qpat_abbrev_tac `new_events = events ++ _` >>
        qexists_tac `new_events` >> xsimpl) >>
     qmatch_goalsub_abbrev_tac` _ * IOx _ fs'` >>
     qmatch_goalsub_abbrev_tac`W8ARRAY _ (_::m1 :: m0 :: n2w i :: rest)` >>
     fs[] >>
     NTAC 3 (xlet_auto >- xsimpl) >> xif >> fs[FALSE_def] >> instantiate >>
     NTAC 2 (xlet_auto >- xsimpl) >>
     fs[GSYM n2w2_def] >>
     `(if n < k then n else k) < (2**(2*8))` by fs[] >>
     progress w22n_n2w2 >>
     xif >> fs[FALSE_def] >> instantiate >> xvar >> xsimpl >>
     fs[IOFS_def,wfFS_fsupdate,liveFS_fsupdate] >>
     instantiate >> fs[Abbr`fs'`,MIN_DEF,insert_atI_def] >> xsimpl) >>
 (* next element is 0 *)
  cases_on`ll` >- fs[liveFS_def,live_numchars_def] >>
  NTAC 2 (xlet_auto >- (xsimpl >> EVAL_TAC >> fs[LUPDATE_def])) >>
  xlet`POSTv uv. &(UNIT_TYPE () uv) * W8ARRAY iobuff_loc (0w:: 0w :: 0w :: n2w i :: rest) *
        IOx fs_ffi_part (fsupdate fs fd 1 pos
                          (TAKE pos content ++
                           TAKE 0 (MAP (CHR o w2n) (DROP i rest)) ++
                           DROP pos content))`
  >-(qmatch_goalsub_abbrev_tac` _ * _ * IOx _ fs'` >>
     qpat_abbrev_tac `Q = $POSTv _` >>
     simp [fs_ffi_part_def, IOx_def, IO_def] >>
     xpull >> qunabbrev_tac `Q` >>
     xffi >> xsimpl >>
     fs[IOFS_def,IOx_def,fs_ffi_part_def,
            mk_ffi_next_def,IO_def] >>
     qmatch_goalsub_abbrev_tac `FFI_part st f ns` >>
     CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
     map_every qexists_tac[`events`,`ns`,`f`,`st`] >> xsimpl >>
     qexists_tac`n2w8 fd` >>
     fs[Abbr`f`,Abbr`st`,Abbr`ns`,mk_ffi_next_def,
        ffi_write_def,(* decode_encode_FS, *)MEM_MAP, ORD_BOUND,ORD_eq_0,wfFS_LDROP,
        dimword_8, MAP_MAP_o,o_DEF,char_BIJ,implode_explode,LENGTH_explode,
        HD_LUPDATE,LUPDATE_def,option_eq_some,validFD_def,write_def,
        get_file_content_def,w82n_n2w8,LENGTH_n2w8] >>
     pairarg_tac >> xsimpl >>
     `MEM fd (MAP FST fs.infds)` by (metis_tac[MEM_MAP]) >>
     rw[] >> TRY(metis_tac[STRING_TYPE_def,wfFS_fsupdate,liveFS_fsupdate,Abbr`fs'`]) >>
     fs[Abbr`fs'`,fsupdate_def,insert_atI_def,n2w2_def] >>
     fs[GSYM n2w2_def] >>
     `i < 2 ** (2 * 8)` by fs[] >> imp_res_tac w22n_n2w2 >>
     `n < 2 ** (2 * 8)` by fs[] >> imp_res_tac w22n_n2w2 >>
     rw[] >> rfs[]
     \\ Cases_on`md` \\ fs[]
     >- rfs[get_mode_def]
     \\ xsimpl >>
     qpat_abbrev_tac `new_events = events ++ _` >>
     qexists_tac `new_events` >> xsimpl) >>
  NTAC 3 (xlet_auto >- xsimpl) >>
  xif >> fs[FALSE_def] >> instantiate >>
  NTAC 2 (xlet_auto >- xsimpl) >>
  fs[w22n_def] >> xif >> fs[TRUE_def] >> instantiate >>
  qmatch_goalsub_abbrev_tac` _ * IOx _ fs'` >>
  xapp >> xsimpl >>
  CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
  qexists_tac`fs'` >> xsimpl >>
  (* hypotheses for induction call *)
  sg`t = fs'.numchars` >-(
    fs[Abbr`fs'`,fsupdate_def,get_file_content_def] >>
    pairarg_tac \\ fs[LDROP_1]) >>
  sg`fs' = fs with numchars := t`
  >-(imp_res_tac validFD_ALOOKUP >> fs[wfFS_def,Abbr`fs'`,fsupdate_def] >>
     fs[IO_fs_component_equality] >> fs[wfFS_def,get_file_content_def] >>
     pairarg_tac >> fs[ALIST_FUPDKEY_unchanged,LDROP_1]) >>
  fs[Abbr`fs'`,get_file_content_def,liveFS_def,live_numchars_def,fsupdate_def,LDROP_1,
     wfFS_fsupdate,validFD_def,liveFS_fsupdate,IOFS_def] >>
  pairarg_tac >> fs[ALIST_FUPDKEY_unchanged] >>
  fs[wfFS_def,liveFS_def,live_numchars_def] >>
  imp_res_tac always_thm >>
  `Lnext_pos (0:::t) = SUC(Lnext_pos t)` by
    (fs[Lnext_pos_def,Once Lnext_def]) >>
  csimp[ADD] >> xsimpl >> cases_on`t` >>
  fs[get_mode_def] >> rw[] >> instantiate >> xsimpl);

Theorem write_spec
  `!n fs fd i pos h1 h2 h3 h4 rest bc fdv nv iv content.
   wfFS fs ⇒ MAX(i + n) 2048 <= LENGTH rest ⇒ i + n < 256 ** 2 ⇒
   get_file_content fs fd = SOME(content, pos) ⇒
   get_mode fs fd = SOME WriteMode ⇒
   FD fd fdv ⇒ NUM n nv ⇒ NUM i iv ⇒
   bc = h1 :: h2 :: h3 :: h4 :: rest ⇒
   app (p:'ffi ffi_proj) TextIO_write_v [fdv;nv;iv]
   (IOx fs_ffi_part fs * W8ARRAY iobuff_loc bc)
   (POSTv nwv. SEP_EXISTS k.
      IOFS(fsupdate fs fd k (pos + n)
                    (insert_atI (TAKE n (MAP (CHR o w2n) (DROP i rest))) pos
                                     content)))`
  (strip_tac >> `?N. n <= N` by (qexists_tac`n` >> fs[]) >>
  FIRST_X_ASSUM MP_TAC >> qid_spec_tac`n` >>
  Induct_on`N` >>
  xcf_with_def "TextIO.write" TextIO_write_v_def
  >>(xlet_auto >- xsimpl >> xif
         >-(TRY instantiate >> xcon >>
                simp[IOFS_iobuff_def,IOFS_def] >> xsimpl >> qexists_tac`0` >>
            fs[fsupdate_unchanged,insert_atI_def] >> xsimpl)) >>
  xlet_auto >> xsimpl
  >-(simp[] >> xsimpl >> rw[] >> instantiate >> xsimpl) >>
  xlet_auto >- xsimpl >> reverse xif
  >-(xcon >> xsimpl >> fs[IOFS_def,IOFS_iobuff_def] >> xsimpl >>
         qexists_tac`(Lnext_pos fs.numchars + 1)` >> `nw = n` by fs[] >> xsimpl >>
     imp_res_tac get_file_content_validFD >>
     fs[wfFS_fsupdate,validFD_def,always_DROP,ALIST_FUPDKEY_ALOOKUP,
        liveFS_fsupdate,get_file_content_def,LENGTH_n2w2]) >>
  NTAC 2 (xlet_auto >- xsimpl) >>
  qmatch_goalsub_abbrev_tac`IOx _ fs'` >>
  `n - nw<= N` by fs[] >>
  FIRST_X_ASSUM (ASSUME_TAC o Q.SPECL[`n-nw`]) >> rfs[] >>
  FIRST_X_ASSUM(ASSUME_TAC o Q.SPECL[`fs'`, `fd`,`nw + i`,`pos+nw`]) >>
  FIRST_X_ASSUM xapp_spec >> xsimpl >> fs[n2w2_def] >>
  qexists_tac`insert_atI (TAKE nw (MAP (CHR ∘ w2n) (DROP i rest))) pos content` >>
  NTAC 3 (strip_tac >-(
      imp_res_tac get_file_content_validFD >>
                  fs[Abbr`fs'`,liveFS_def,live_numchars_def,LDROP_1, wfFS_fsupdate,validFD_def,
                         always_DROP,ALIST_FUPDKEY_ALOOKUP,get_file_content_def,get_mode_def] >>
                  pairarg_tac >> fs[fsupdate_def,always_DROP,ALIST_FUPDKEY_ALOOKUP] >>
          imp_res_tac NOT_LFINITE_DROP >>
          FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC`(Lnext_pos fs.numchars + 1)`) >>
          fs[] >> imp_res_tac NOT_LFINITE_DROP_LFINITE)) >>
  rw[] >> qexists_tac`Lnext_pos fs.numchars + 1 + x` >>
  fs[wfFS_def,fsupdate_o,Abbr`fs'`,insert_atI_insert_atI] >>
  qmatch_abbrev_tac`_ (_ _ _ _ _ (_ c1 _ _)) ==>> _ (_ _ _ _ _ (_ c2 _ _)) * _` >>
  `c1 = c2` suffices_by xsimpl >> fs[Abbr`c1`,Abbr`c2`] >>
  PURE_REWRITE_TAC[Once (Q.SPECL [`i`,`nw`] ADD_COMM)] >>
  fs[Once ADD_COMM,GSYM DROP_DROP_T,take_drop_partition,MAP_DROP]);

Theorem output1_spec
  `!fd fdv c cv bc content pos.
    get_file_content fs fd = SOME(content, pos) ⇒
    get_mode fs fd = SOME WriteMode ⇒
    CHAR c cv ⇒ OUTSTREAM fd fdv ⇒
    app (p:'ffi ffi_proj) TextIO_output1_v [fdv; cv]
    (IOFS fs)
    (POSTv uv.
      &UNIT_TYPE () uv * SEP_EXISTS k.
      IOFS (fsupdate fs fd k (pos+1) (insert_atI [c] pos content)))`
  (xcf_with_def "TextIO.output1" TextIO_output1_v_def >>
  fs[IOFS_def,IOFS_iobuff_def] >>
  xpull >> rename [`W8ARRAY _ bdef`] >>
  ntac 3 (xlet_auto >- xsimpl) >>
  fs [OUTSTREAM_def] >>
  xlet_auto >- xsimpl >> fs [get_out_def] >>
  Cases_on `bdef` >> fs[] >> qmatch_goalsub_rename_tac`h1 :: t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1 :: h2 :: t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1 :: h2 :: h3 :: t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1 :: h2 :: h3 :: h4 :: t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1 :: h2 :: h3 :: h4 :: h5 :: t` >>
  simp[LUPDATE_compute] >>
  xlet_auto >-(xsimpl >> fs [FD_def]) >>
  xcon >> fs[IOFS_def,IOFS_iobuff_def] >> xsimpl >> rw[] >>
  fs[CHR_ORD,LESS_MOD,ORD_BOUND] >> qexists_tac`k` >> xsimpl);

Theorem output1_STDIO_spec
  `!fd. get_file_content fs fd = SOME(content, pos) ∧
        get_mode fs fd = SOME WriteMode ∧
   CHAR c cv ∧ OUTSTREAM fd fdv ⇒
   app (p:'ffi ffi_proj) TextIO_output1_v [fdv; cv]
   (STDIO fs)
   (POSTv uv.
     &UNIT_TYPE () uv *
     STDIO (fsupdate fs fd 0 (pos+1) (insert_atI [c] pos content)))`
  (rw[STDIO_def] \\ xpull \\ xapp_spec output1_spec \\
  mp_tac(SYM(SPEC_ALL get_file_content_numchars)) \\ rw[] \\
  mp_tac(get_mode_with_numchars) \\ rw[] \\
  instantiate \\ simp[GSYM validFD_numchars] \\ xsimpl \\ rw[] \\
  qexists_tac`THE (LDROP x ll)` \\
  conj_tac >- (
    match_mp_tac STD_streams_fsupdate \\ fs[] \\
    fs[STD_streams_def,get_file_content_def] \\
    pairarg_tac \\ fs[] \\
    first_x_assum(qspecl_then[`2`,`WriteMode`,`LENGTH err`]mp_tac) \\
    first_x_assum(qspecl_then[`1`,`WriteMode`,`LENGTH out`]mp_tac) \\
    rw[] \\ rfs[] \\ rw[] \\ fs[] \\
    simp[insert_atI_def,LENGTH_TAKE_EQ] )
  \\ qmatch_abbrev_tac`IOFS fs1 ==>> IOFS fs2 * _`
  \\ `fs1 = fs2` suffices_by xsimpl
  \\ fs[get_file_content_def] \\ pairarg_tac \\ fs[]
  \\ rw[Abbr`fs1`,Abbr`fs2`,IO_fs_component_equality,fsupdate_def]);

val tac =
     simp[w82n_n2w8,FD_def,LENGTH_n2w8,STRING_TYPE_def] \\ xsimpl
  \\ imp_res_tac STD_streams_stdout
  \\ imp_res_tac STD_streams_stderr
  \\ simp[add_stdo_def,up_stdo_def]
  \\ SELECT_ELIM_TAC \\ conj_tac >- metis_tac[]
  \\ rw[] \\ imp_res_tac stdo_UNICITY_R \\ rveq
  \\ fs[stdo_def,get_file_content_def,get_mode_def,PULL_EXISTS]
  \\ instantiate \\ xsimpl
  \\ conj_tac >- (EVAL_TAC \\ simp[EVAL_RULE stdout_v_thm,EVAL_RULE stderr_v_thm])
  \\ simp[Q.ISPEC`explode x`(Q.GEN`l2`insert_atI_end) |> SIMP_RULE(srw_ss())[]]
  \\ xsimpl;

Theorem output1_stdout_spec
  `CHAR c cv ∧ fdv = stdout_v ==>
   app (p:'ffi ffi_proj) TextIO_output1_v
     [fdv; cv] (STDIO fs)
     (POSTv uv. &UNIT_TYPE () uv * STDIO (add_stdout fs (str c)))`
  (reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ strip_tac \\ xpull)
  \\ strip_tac
  \\ xapp_spec output1_STDIO_spec
  \\ tac);

Theorem output1_stderr_spec
  `CHAR c cv ∧ fdv = stderr_v ==>
   app (p:'ffi ffi_proj) TextIO_output1_v
     [fdv; cv] (STDIO fs)
     (POSTv uv. &UNIT_TYPE () uv * STDIO (add_stderr fs (str c)))`
  (reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ strip_tac \\ xpull)
  \\ strip_tac
  \\ xapp_spec output1_STDIO_spec
  \\ tac);

Theorem output_spec
  `!s fd fdv sv fs content pos.
    OUTSTREAM fd fdv ⇒ STRING_TYPE s sv ⇒
    (get_file_content fs fd = SOME(content, pos)) ⇒
    (get_mode fs fd = SOME WriteMode) ⇒
    app (p:'ffi ffi_proj) TextIO_output_v [fdv; sv]
    (IOFS fs)
    (POSTv uv. &(UNIT_TYPE () uv) *
       SEP_EXISTS k. IOFS (fsupdate fs fd k (pos + (strlen s))
                                    (insert_atI (explode s) pos content)))`
  (strip_tac >>
  `?n. strlen s <= n` by (qexists_tac`strlen s` >> fs[]) >>
  FIRST_X_ASSUM MP_TAC >> qid_spec_tac`s` >>
  Induct_on`n` >>
  xcf_with_def "TextIO.output" TextIO_output_v_def >>
  fs[IOFS_def,IOFS_iobuff_def] >>
  xpull >> rename [`W8ARRAY _ buff`] >>
  Cases_on `buff` >> fs[] >> qmatch_goalsub_rename_tac`h1 :: t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1 :: h2 :: t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::h3::t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::h3::h4::t` >>
  (xlet_auto >- xsimpl) >>
  (xif >-(xcon >> xsimpl >> qexists_tac`0` >>
         fs[fsupdate_unchanged,insert_atI_NIL] >> xsimpl))
  >-(cases_on`s` >> fs[strlen_def]) >>
  fs[insert_atI_def] >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  xlet`POSTv mv. &NUM (MIN (strlen s) 2048) mv * IOx fs_ffi_part fs * W8ARRAY
  (iobuff_loc) (h1::h2::h3::h4::t)`
  >- (
    xif
    >- (xret \\ xsimpl \\ fs[NUM_def,INT_def,MIN_DEF] )
    \\ xlit \\ xsimpl \\ fs[MIN_DEF] ) >>
  xlet_auto >- xsimpl >>
  fs[insert_atI_def] >>
  fs [OUTSTREAM_def] >>
  xlet_auto >- xsimpl >> fs [get_out_def] >>
  xlet_auto >> xsimpl
  >-(xsimpl >> fs[LENGTH_explode,strlen_substring,FD_def]) >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  qmatch_goalsub_abbrev_tac`fsupdate fs _ _ pos' content'` >>
  qmatch_goalsub_abbrev_tac`IOFS fs'` >>
  fs[IOFS_def] >> xpull >>
  xapp >> fs[IOFS_iobuff_def,IOFS_def] >> xsimpl >>
  CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
  map_every qexists_tac [`content'`,`fd`,`fs'`,`pos'`] >>
  instantiate >> xsimpl >>
  `strlen s <> 0` by (cases_on`s` >> cases_on`s'` >> fs[])>>
  fs[strlen_substring] >>
  imp_res_tac get_file_content_validFD >>
  fs[get_file_content_def, get_mode_def] >> pairarg_tac >>
  fs[Abbr`fs'`,Abbr`pos'`,Abbr`content'`,liveFS_def,live_numchars_def,
     fsupdate_def,LDROP_1, wfFS_fsupdate,validFD_def,always_DROP,
     ALIST_FUPDKEY_ALOOKUP,extract_def,strlen_extract_le,
     MIN_DEF] >> xsimpl >>
  rpt strip_tac >>
  qexists_tac`x' + k` >> fs[insert_atI_def] >>
  qmatch_goalsub_abbrev_tac`IOx _ fs1 ==>> IOx _ fs2 * GC` >>
  `fs1 = fs2` suffices_by xsimpl >> fs[Abbr`fs1`,Abbr`fs2`] >>
  simp[IO_fs_component_equality] >>
  reverse conj_tac >- (
    reverse conj_tac >- (
      fs[LDROP_ADD] \\
      CASE_TAC \\ fs[] \\
      imp_res_tac LDROP_NONE_LFINITE
      \\ fs[wfFS_def,liveFS_def,live_numchars_def] ) >>
    fs[ALIST_FUPDKEY_o] >>
    match_mp_tac ALIST_FUPDKEY_eq >>
    fs[PAIR_MAP_THM,FORALL_PROD] ) >>
  fs[ALIST_FUPDKEY_o] >>
  match_mp_tac ALIST_FUPDKEY_eq >>
  simp[] >>
  fs[MAP_MAP_o,CHR_w2n_n2w_ORD] >>
  IF_CASES_TAC >-
    fs[substring_too_long,TAKE_APPEND,TAKE_TAKE,TAKE_LENGTH_TOO_LONG,
       LENGTH_explode,DROP_APPEND,LENGTH_TAKE_EQ,DROP_LENGTH_TOO_LONG] >>
  fs[LENGTH_explode,strlen_substring] >>
  fs[TAKE_APPEND,DROP_APPEND,LENGTH_TAKE_EQ,LENGTH_explode,
     strlen_substring,DROP_LENGTH_TOO_LONG,TAKE_LENGTH_ID_rwt] >>
  IF_CASES_TAC \\
  fs[TAKE_LENGTH_ID_rwt,LENGTH_explode,strlen_substring,
     DROP_DROP_T,TAKE_LENGTH_TOO_LONG,DROP_LENGTH_TOO_LONG]
  \\ Cases_on`s` \\ fs[substring_def,SEG_TAKE_DROP,TAKE_LENGTH_ID_rwt]);

Theorem output_STDIO_spec
  `!fd fdv fs content pos s.
   OUTSTREAM fd fdv ∧ get_file_content fs fd = SOME (content,pos) ∧ get_mode fs fd = SOME WriteMode ∧ STRING_TYPE s sv ⇒
   app (p:'ffi ffi_proj) TextIO_output_v [fdv;sv]
   (STDIO fs)
   (POSTv uv. &(UNIT_TYPE () uv) *
      STDIO (fsupdate fs fd 0 (pos+strlen s) (insert_atI (explode s) pos content)))`
  (rpt strip_tac
  \\ fs[STDIO_def]
  \\ xpull
  \\ xapp_spec output_spec
  \\ first_x_assum(assume_tac o CONV_RULE(LAND_CONV(REWR_CONV get_file_content_numchars)))
  \\ first_x_assum(assume_tac o CONV_RULE(LAND_CONV(REWR_CONV (SYM get_mode_with_numchars))))
  \\ instantiate \\ xsimpl
  \\ fs[get_file_content_def]
  \\ simp[Once fsupdate_0_numchars,SimpR``$/\``]
  \\ simp[fsupdate_numchars]
  \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`_ with numchars := ns`
  \\ qexists_tac`ns` \\ xsimpl
  \\ DEP_REWRITE_TAC[STD_streams_fsupdate] \\ fs[]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ `fd = 1 ∨ fd = 2 ⇒ off = LENGTH content`
  by (
    fs[STD_streams_def]
    \\ metis_tac[SOME_11,PAIR,FST,SND] ) \\
  rw[] \\ fs[] \\ simp[insert_atI_end,LENGTH_explode]);

Theorem print_spec
  `!fs sv s.
    STRING_TYPE s sv ⇒
    app (p:'ffi ffi_proj) TextIO_print_v [sv]
    (STDIO fs)
    (POSTv uv. &(UNIT_TYPE () uv) * STDIO (add_stdout fs s))`
  (xcf_with_def "TextIO.print" TextIO_print_v_def
  \\ reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull)
  \\ xapp_spec output_STDIO_spec
  \\ tac);

val print_def = Define `
  print s = (\fs. (Success (), add_stdout fs s))`

Theorem EvalM_print
  `Eval env exp (STRING_TYPE x) /\
   (nsLookup env.v (Short "print") = SOME TextIO_print_v) ==>
    EvalM F env st (App Opapp [Var (Short "print"); exp])
      (MONAD UNIT_TYPE exc_ty (print x))
      (MONAD_IO,p:'ffi ffi_proj)`
  (ho_match_mp_tac EvalM_from_app \\ rw [print_def]
  \\ fs [MONAD_IO_def]
  \\ xpull
  \\ fs [SEP_CLAUSES]
  \\ match_mp_tac (app_weaken |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO])
  \\ drule (GEN_ALL print_spec)
  \\ disch_then (qspecl_then [`p`,`s`] assume_tac)
  \\ asm_exists_tac \\ fs []
  \\ xsimpl);

Theorem output_stderr_spec
  `!fs sv s fdv.
    STRING_TYPE s sv ∧ fdv = stderr_v ⇒
    app (p:'ffi ffi_proj) TextIO_output_v [fdv;sv]
    (STDIO fs)
    (POSTv uv. &(UNIT_TYPE () uv) * STDIO (add_stderr fs s))`
  (rpt strip_tac
  \\ reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull)
  \\ xapp_spec output_STDIO_spec
  \\ tac);

Theorem print_err_spec
  `!fs sv s.
    STRING_TYPE s sv ⇒
    app (p:'ffi ffi_proj) TextIO_print_err_v [sv]
    (STDIO fs)
    (POSTv uv. &(UNIT_TYPE () uv) * STDIO (add_stderr fs s))`
  (xcf_with_def "TextIO.print_err" TextIO_print_err_v_def
  \\ reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull)
  \\ xapp_spec output_stderr_spec \\ fs []);

val print_err_def = Define `
  print_err s = (\fs. (Success (), add_stderr fs s))`;

Theorem EvalM_print_err
  `Eval env exp (STRING_TYPE x) /\
    (nsLookup env.v (Long "TextIO" (Short "print_err")) =
      SOME TextIO_print_err_v) ==>
    EvalM F env st (App Opapp [Var (Long "TextIO" (Short "print_err")); exp])
      (MONAD UNIT_TYPE exc_ty (print_err x))
      (MONAD_IO,p:'ffi ffi_proj)`
  (ho_match_mp_tac EvalM_from_app \\ rw [print_err_def]
  \\ fs [MONAD_IO_def]
  \\ xpull
  \\ fs [SEP_CLAUSES]
  \\ match_mp_tac (app_weaken |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO])
  \\ drule (GEN_ALL print_err_spec)
  \\ disch_then (qspecl_then [`p`,`s`] assume_tac)
  \\ asm_exists_tac \\ fs []
  \\ xsimpl);

Theorem read_spec
  `!fs fd fdv n nv. wfFS fs ⇒ FD fd fdv ⇒ NUM n nv ⇒
   n < 256**2 ⇒ MAX n 2048 <= LENGTH rest ⇒
   app (p:'ffi ffi_proj) TextIO_read_v [fdv;nv]
   (W8ARRAY iobuff_loc (h1::h2::h3::h4::rest) * IOx fs_ffi_part fs)
   (POSTve
     (\nrv. SEP_EXISTS (nr : num).
      &(NUM nr nrv) *
      SEP_EXISTS content pos.
        &(get_file_content fs fd = SOME(content, pos) /\
          get_mode fs fd = SOME ReadMode /\
          (nr <= MIN n (LENGTH content - pos)) /\
          (nr = 0 ⇔ eof fd fs = SOME T ∨ n = 0)) *
      IOx fs_ffi_part (bumpFD fd fs nr) *
      W8ARRAY iobuff_loc (0w :: n2w (nr DIV 256) :: n2w nr :: h4::
        MAP (n2w o ORD) (TAKE nr (DROP pos content))++DROP nr rest))
     (\e. &InvalidFD_exn e * &(get_file_content fs fd = NONE ∨ get_mode fs fd ≠ SOME ReadMode) * IOFS fs))`
   (xcf_with_def "TextIO.read" TextIO_read_v_def >>
   fs[IOFS_def,IOFS_iobuff_def] >>
   xlet_auto >- xsimpl >>
   simp[insert_atI_def,n2w2_def] >>
   cases_on`get_file_content fs fd`
   >-(xlet`POSTv v. W8ARRAY iobuff_loc (1w::n2w n::h3::h4::rest) * IOx fs_ffi_part fs`
      >-(qpat_abbrev_tac `Q = $POSTv _` >>
         simp [fs_ffi_part_def, IOx_def, IO_def] >>
         xpull >> qunabbrev_tac `Q` >>
         xffi >> xsimpl >>
         fs[IOFS_def,IOx_def,fs_ffi_part_def, mk_ffi_next_def,IO_def] >>
         qmatch_goalsub_abbrev_tac `FFI_part st f ns` >>
         CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
         map_every qexists_tac[`events`,`ns`,`f`, `st`] >>
         xsimpl >> qexists_tac`n2w8 fd` >>
         fs[Abbr`f`,Abbr`st`,Abbr`ns`,mk_ffi_next_def, ffi_read_def,
            w82n_n2w8,LENGTH_n2w8,MEM_MAP, ORD_BOUND,ORD_eq_0,wfFS_LDROP,
            dimword_8, MAP_MAP_o,o_DEF,char_BIJ,implode_explode,LENGTH_explode,
            HD_LUPDATE,LUPDATE_def,option_eq_some,validFD_def,read_def,
            get_file_content_def,n2w_w2n,w2n_n2w,FD_def,STRING_TYPE_def] >> rfs[] >>
         `n < 2 ** (2 * 8)` by fs[] >> imp_res_tac w22n_n2w2 >>
         fs[n2w2_def] >> xsimpl >>
         TRY (pairarg_tac >> fs[] >>
              TRY(Cases_on`md`) >> fs[] >> xsimpl) >>
         qpat_abbrev_tac `new_events = events ++ _` >>
         qexists_tac `new_events` >> xsimpl) >>
      rpt(xlet_auto >- xsimpl) >> xif >> instantiate >>
      xlet_auto >-(xcon >> xsimpl >> instantiate >> xsimpl) >>
      xraise >> xsimpl >> fs[InvalidFD_exn_def] >> xsimpl) >>
   cases_on`x` >> fs[] >>
   cases_on`get_mode fs fd`
   >- fs[get_mode_def, get_file_content_def] >>
   reverse(cases_on`x` >> fs[])
   >-(xlet`POSTv v. W8ARRAY iobuff_loc (1w::n2w n::h3::h4::rest) * IOx fs_ffi_part fs`
      >-(qpat_abbrev_tac `Q = $POSTv _` >>
         simp [fs_ffi_part_def, IOx_def, IO_def] >>
         xpull >> qunabbrev_tac `Q` >>
         xffi >> xsimpl >>
         fs[IOFS_def,IOx_def,fs_ffi_part_def, mk_ffi_next_def,IO_def] >>
         qmatch_goalsub_abbrev_tac `FFI_part st f ns` >>
         CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
         map_every qexists_tac[`events`,`ns`,`f`,`st`] >>
         xsimpl >> qexists_tac`n2w8 fd` >>
         fs[Abbr`f`,Abbr`st`,Abbr`ns`,mk_ffi_next_def, ffi_read_def,
            w82n_n2w8,LENGTH_n2w8,MEM_MAP, ORD_BOUND,ORD_eq_0,wfFS_LDROP,
            dimword_8, MAP_MAP_o,o_DEF,char_BIJ,implode_explode,LENGTH_explode,
            HD_LUPDATE,LUPDATE_def,option_eq_some,validFD_def,read_def,
            get_file_content_def,n2w_w2n,w2n_n2w,FD_def,STRING_TYPE_def] >> rfs[] >>
         `n < 2 ** (2 * 8)` by fs[] >> imp_res_tac w22n_n2w2 >>
         rfs[get_mode_def] >>
         fs[n2w2_def] >> xsimpl >>
         pairarg_tac >> fs[] >> xsimpl >>
         qpat_abbrev_tac `new_events = events ++ _` >>
         qexists_tac `new_events` >> xsimpl) >>
      rpt(xlet_auto >- xsimpl) >> xif >> instantiate >>
      xlet_auto >-(xcon >> xsimpl >> instantiate >> xsimpl) >>
      xraise >> xsimpl >> fs[InvalidFD_exn_def] >> xsimpl) >>
   xlet `POSTve (\uv. SEP_EXISTS nr nrv . &(NUM nr nrv) *
      SEP_EXISTS content pos.  &(get_file_content fs fd = SOME(content, pos) /\
          get_mode fs fd = SOME ReadMode /\
          (nr <= MIN n (LENGTH content - pos)) /\
          (nr = 0 ⇔ eof fd fs = SOME T ∨ n = 0)) *
        IOx fs_ffi_part (bumpFD fd fs nr) *
        W8ARRAY iobuff_loc (0w :: n2w (nr DIV 256) :: n2w nr :: h4 ::
          (MAP (n2w o ORD) (TAKE nr (DROP pos content))++DROP nr rest)))
          (\e. &(get_file_content fs fd = NONE))` >> xsimpl
   >-(qpat_abbrev_tac `Q = POSTve _ _` >>
      simp [fs_ffi_part_def, IOx_def, IO_def] >>
      xpull >> qunabbrev_tac `Q` >>
      xffi >> xsimpl >>
      fs[IOFS_def,IOx_def,fs_ffi_part_def, mk_ffi_next_def,IO_def] >>
      qmatch_goalsub_abbrev_tac `FFI_part st f ns` >>
      CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
      map_every qexists_tac[`events`,`ns`,`f`,`st`] >>
      xsimpl >> qexists_tac`n2w8 fd` >>
      fs[Abbr`f`,Abbr`st`,Abbr`ns`,mk_ffi_next_def,
         ffi_read_def,w82n_n2w8,LENGTH_n2w8,MEM_MAP, ORD_BOUND,ORD_eq_0,wfFS_LDROP,
         dimword_8, MAP_MAP_o,o_DEF,char_BIJ,implode_explode,LENGTH_explode,
         HD_LUPDATE,LUPDATE_def,option_eq_some,validFD_def,read_def,
         get_file_content_def,FD_def,STRING_TYPE_def] >> rfs[get_mode_def] >>
      simp[GSYM n2w2_def,w22n_n2w2] >>
      pairarg_tac >> xsimpl >> fs[] >> rw[] >>
      cases_on`fs.numchars` >> fs[wfFS_def,liveFS_def,live_numchars_def] >>
      fs[n2w2_def,DIV_MOD_MOD_DIV,DIV_DIV_DIV_MULT] >> xsimpl >>
      qmatch_goalsub_abbrev_tac`(k DIV 256) MOD 256 = _ MOD 256` >> qexists_tac`k` >>
      xsimpl >> fs[MIN_LE,eof_def,Abbr`k`,NUM_def,INT_def] >>
      qpat_abbrev_tac `new_events = events ++ _` >>
      qexists_tac `new_events` >> xsimpl) >>
   rpt(xlet_auto >- xsimpl) >>
   xif >> instantiate >> xapp >> xsimpl >> rw[] >> instantiate >>
   simp[GSYM n2w2_def,w22n_n2w2] >> xsimpl);

Theorem read_byte_spec
  `!fd fdv content pos.
    FD fd fdv ⇒
    get_file_content fs fd = SOME(content, pos) ⇒
    get_mode fs fd = SOME ReadMode ⇒
    app (p:'ffi ffi_proj) TextIO_read_byte_v [fdv]
    (IOFS fs)
    (POSTve
      (\cv. &(WORD (n2w (ORD (EL pos content)):word8) cv /\
            eof fd fs = SOME F) *
            IOFS (bumpFD fd fs 1))
      (\e.  &(EndOfFile_exn e /\ eof fd fs = SOME T) *
            IOFS(bumpFD fd fs 0)))`
  (xcf_with_def "TextIO.read_byte" TextIO_read_byte_v_def >>
  fs[IOFS_def,IOFS_iobuff_def] >>
  xpull >> rename [`W8ARRAY _ bdef`] >>
  Cases_on `bdef` >> fs[] >> qmatch_goalsub_rename_tac`h1 :: t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::h3::t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::h3::h4::t` >>
  xlet_auto >-(fs[] >> xsimpl >> rw[] >> instantiate >> xsimpl)
  >- xsimpl >>
  xlet_auto >- xsimpl >>
  xif >-(xlet_auto >- (xcon >> xsimpl) >> xraise >>
         fs[EndOfFile_exn_def,eof_def,get_file_content_def,liveFS_bumpFD] >> xsimpl) >>
  xapp >> xsimpl >>
  `nr = 1` by fs[] >> fs[] >> xsimpl >>
  fs[TAKE1_DROP,eof_def,get_file_content_def] >> pairarg_tac >> fs[liveFS_bumpFD]);

Theorem read_byte_STDIO_spec
  ` FD fd fdv ∧ fd ≠ 1 ∧ fd ≠ 2 ∧
    get_file_content fs fd = SOME(content, pos) ⇒
    get_mode fs fd = SOME ReadMode ⇒
    app (p:'ffi ffi_proj) TextIO_read_byte_v [fdv]
    (STDIO fs)
    (POSTve
      (\cv. &(WORD (n2w (ORD (EL pos content)):word8) cv /\
            eof fd fs = SOME F) *
            STDIO (bumpFD fd fs 1))
      (\e.  &(EndOfFile_exn e /\ eof fd fs = SOME T) *
            STDIO(bumpFD fd fs 0)))`
  (rw[STDIO_def] >> xpull >> xapp_spec read_byte_spec >>
  mp_tac(GSYM(SPEC_ALL get_file_content_numchars)) >> rw[] >>
  mp_tac(get_mode_with_numchars) >> rw[] >>
  instantiate >> xsimpl >>
  simp[bumpFD_forwardFD,forwardFD_numchars,STD_streams_forwardFD] \\
  rw[] \\ qexists_tac`THE (LTL ll)` \\ xsimpl);

(* TODO: call the low-level IOFS specs with the non-standard name, not vice versa *)

Theorem input1_spec
  ` INSTREAM fd fdv ∧ fd ≠ 1 ∧ fd ≠ 2 ∧
    get_file_content fs fd = SOME(content, pos) ⇒
    get_mode fs fd = SOME ReadMode ⇒
    app (p:'ffi ffi_proj) TextIO_input1_v [fdv]
    (STDIO fs)
    (POSTv v.
      case eof fd fs of
      | SOME F =>
        &OPTION_TYPE CHAR (SOME (EL pos content)) v *
        STDIO (bumpFD fd fs 1)
      | SOME T =>
        &OPTION_TYPE CHAR NONE v *
        STDIO (bumpFD fd fs 0)
      | _ => &F)`
  (xcf_with_def "TextIO.input1" TextIO_input1_v_def
  \\ xhandle`POSTve (λv. &OPTION_TYPE CHAR (SOME (EL pos content)) v *
                         STDIO (forwardFD fs fd 1) * &(eof fd fs = SOME F))
                    (λe. &EndOfFile_exn e * STDIO fs * &(eof fd fs = SOME T))`
  >- (
    fs [INSTREAM_def]
    \\ xlet_auto >- xsimpl \\ fs [get_in_def]
    \\ xlet_auto_spec(SOME read_byte_STDIO_spec)
    \\ xsimpl \\ simp[bumpFD_0,FD_def] \\ xsimpl
    \\ xlet_auto \\ xsimpl
    \\ xlet_auto \\ xsimpl
    \\ xcon \\ xsimpl
    \\ fs[ORD_BOUND,CHR_ORD,std_preludeTheory.OPTION_TYPE_def] )
  \\ xsimpl
  \\ xcases
  \\ xsimpl
  \\ fs[EndOfFile_exn_def]
  \\ reverse conj_tac >- (EVAL_TAC \\ fs[])
  \\ xcon
  \\ xsimpl
  \\ fs[std_preludeTheory.OPTION_TYPE_def]);

Theorem input_IOFS_spec
  `!fd fdv fs content pos off offv.
    len + off <= LENGTH buf ∧
    INSTREAM fd fdv ∧ NUM off offv ∧ NUM len lenv ∧
    get_file_content fs fd = SOME(content, pos) ⇒
    get_mode fs fd = SOME ReadMode ⇒
    app (p:'ffi ffi_proj) TextIO_input_v [fdv; bufv; offv; lenv]
    (IOFS fs * W8ARRAY bufv buf)
    (POSTv nv. &(NUM (MIN len (LENGTH content - pos)) nv) *
       W8ARRAY bufv (insert_atI (TAKE len (DROP pos (MAP (n2w o ORD) content)))
                                 off buf) *
       SEP_EXISTS k. IOFS (fsupdate fs fd k (MIN (len + pos) (MAX pos (LENGTH content))) content))`
  (xcf_with_def "TextIO.input" TextIO_input_v_def >>
  reverse(Cases_on`pos ≤ LENGTH content`) >- (
    imp_res_tac get_file_content_eof \\ rfs[] \\
    reverse(Cases_on`wfFS fs`) >- (fs[IOFS_def] \\ xpull) \\
    simp[MAX_DEF,MIN_DEF] \\
    xfun_spec`input0`
    `∀offv lenv countv.
     NUM len lenv ∧ NUM 0 countv ⇒
     app (p:'ffi ffi_proj) input0 [offv; lenv; countv]
      (IOFS fs * W8ARRAY bufv buf)
      (POSTv nv. &(NUM 0 nv) * W8ARRAY bufv buf * IOFS (bumpFD fd fs 0))`
    >- (
      rpt strip_tac \\
      first_x_assum match_mp_tac \\
      xlet_auto >- xsimpl \\
      fs[IOFS_def,IOFS_iobuff_def] \\ xpull \\
      qmatch_assum_rename_tac`LENGTH buff >= _` \\
      Cases_on `buff` >> fs[] >> qmatch_goalsub_rename_tac`h1::t` >>
      Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::t` >>
      Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::h3::t` >>
      Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::h3::h4::t` >>
      fs [INSTREAM_def] >>
      xlet_auto >- xsimpl >> fs [get_in_def] >>
      `FD fd sv` by fs [FD_def] >>
      xlet_auto \\ simp[]
      >- xsimpl
      >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ xif
      \\ instantiate
      \\ xvar
      \\ xsimpl )
    \\ `LENGTH content - pos = 0` by decide_tac
    \\ xapp
    \\ xsimpl
    \\ simp[DROP_LENGTH_TOO_LONG,insert_atI_NIL]
    \\ simp[fsupdate_def,bumpFD_def]
    \\ fs[get_file_content_def]
    \\ pairarg_tac \\ fs[] \\ rw[]
    \\ fs[wfFS_def,liveFS_def,live_numchars_def]
    \\ qexists_tac`1`
    \\ Cases_on`fs.numchars` >- fs[]
    \\ simp[LDROP_1]
    \\ qmatch_abbrev_tac`IOFS f1 ==>> IOFS f2 * _`
    \\ `f1 = f2` by (
      simp[Abbr`f1`,Abbr`f2`,IO_fs_component_equality]
      \\ simp[ALIST_FUPDKEY_unchanged] )
    \\ xsimpl )
  \\ `MAX pos (LENGTH content) = LENGTH content` by rw[MAX_DEF]
  \\ pop_assum SUBST_ALL_TAC >>
 xfun_spec`input0`
  `!count countv buf fs pos off offv lenv.
    len + off <= LENGTH buf ⇒ pos <= LENGTH content  ⇒ NUM count countv ⇒
    INSTREAM fd fdv ⇒ NUM off offv ⇒ NUM len lenv ⇒
    get_file_content fs fd = SOME(content, pos) ⇒
    get_mode fs fd = SOME ReadMode ⇒
    app (p:'ffi ffi_proj) input0
        [offv; lenv; countv]
    (IOFS fs * W8ARRAY bufv buf)
    (POSTv nv. &(NUM (count + MIN len (LENGTH content - pos)) nv) *
       W8ARRAY bufv (insert_atI (TAKE len (DROP pos (MAP (n2w o ORD) content)))
                                 off buf) *
       SEP_EXISTS k. IOFS (fsupdate fs fd k (MIN (len + pos) (LENGTH content)) content
))` >-
 (`?N. len <= N` by (qexists_tac`len` >> fs[]) >>
  FIRST_X_ASSUM MP_TAC >> qid_spec_tac`len` >>
  Induct_on`N` >> rw[]
  >-(xapp >> fs[IOFS_def,IOFS_iobuff_def] >> xpull >>
     xlet_auto >- xsimpl >>
     rename [`W8ARRAY iobuff_loc bdef`] >>
     Cases_on `bdef` >> fs[] >> qmatch_goalsub_rename_tac`h1::t` >>
     Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::t` >>
     Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::h3::t` >>
     Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::h3::h4::t` >>
     fs [INSTREAM_def] >>
     xlet_auto >- xsimpl >> fs [get_in_def] >>
     `FD fd sv` by fs [FD_def] >>
     xlet_auto >-(fs[] >> xsimpl) >- xsimpl >>
     xlet_auto >-xsimpl >>
     xif >> instantiate >> xlit >> xsimpl >>
     qexists_tac `1` >>
     fs[get_file_content_def] >> pairarg_tac >> rw[] >>
     fs[wfFS_fsupdate,liveFS_fsupdate,MIN_DEF,MEM_MAP,insert_atI_NIL,
        validFD_ALOOKUP, bumpFD_def, fsupdate_def,LDROP_1,
        ALIST_FUPDKEY_unchanged,wfFS_def,liveFS_def,live_numchars_def] >>
     cases_on`fs'.numchars` >> fs[LDROP_1,NOT_LFINITE_DROP_LFINITE] >>
     cases_on`fs'.numchars` >> fs[LDROP_1] >> cases_on`fs` >>
     qmatch_abbrev_tac`IOx _ fs1 ==>> IOx _ fs2 * GC` >>
     `fs1 = fs2` by (unabbrev_all_tac >>
                     fs[IO_fs_component_equality,ALIST_FUPDKEY_unchanged]) >>
     xsimpl) >>
  last_x_assum xapp_spec>> fs[IOFS_def,IOFS_iobuff_def] >> xpull >>
  rw[] >> cases_on`len'`
  >-(rw[] >>
     xlet_auto >- xsimpl >>
     rename [`W8ARRAY iobuff_loc bdef`] >>
     Cases_on `bdef` >> fs[] >> qmatch_goalsub_rename_tac`h1::t` >>
     Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::t` >>
     Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::h3::t` >>
     Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::h3::h4::t` >>
     fs [INSTREAM_def] >>
     xlet_auto >- xsimpl >> fs [get_in_def] >>
     `FD fd sv` by fs [FD_def] >>
     xlet_auto >-(fs[] >> xsimpl) >- xsimpl >>
     xlet_auto >- xsimpl >> xif >> instantiate >> xlit >> xsimpl >>
     qexists_tac `1` >>
     fs[get_file_content_def] >> pairarg_tac >> rw[] >>
     fs[wfFS_fsupdate,liveFS_fsupdate,MIN_DEF,MEM_MAP,insert_atI_NIL,
        validFD_ALOOKUP, bumpFD_def, fsupdate_def,LDROP_1,
        ALIST_FUPDKEY_unchanged,wfFS_def,liveFS_def,live_numchars_def] >>
     cases_on`fs'.numchars` >> fs[LDROP_1,NOT_LFINITE_DROP_LFINITE] >>
     cases_on`fs'.numchars` >> fs[LDROP_1] >> cases_on`fs` >>
     qmatch_abbrev_tac`IOx _ fs1 ==>> IOx _ fs2 * GC` >>
     `fs1 = fs2` suffices_by xsimpl >>
     unabbrev_all_tac >> fs[IO_fs_component_equality,ALIST_FUPDKEY_unchanged]) >>
  xlet_auto >- xsimpl >>
  rename [`W8ARRAY iobuff_loc bdef`] >>
  Cases_on `bdef` >> fs[] >> qmatch_goalsub_rename_tac`h1::t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::h3::t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::h3::h4::t` >>
  fs [INSTREAM_def] >>
  xlet_auto >- xsimpl >> fs [get_in_def] >>
  `FD fd sv` by fs [FD_def] >>
  xlet_auto
  >-(fs[] >> xsimpl >> rw[] >> TRY instantiate >> xsimpl)
  >- xsimpl >>
  xlet_auto >- xsimpl >>
  `MEM fd (MAP FST fs'.infds)` by
     (fs[get_file_content_def] >> pairarg_tac >> fs[ALOOKUP_MEM,MEM_MAP] >>
      qexists_tac`fd,(fnm, md,pos'')` >> fs[ALOOKUP_MEM]) >>
  xif
  >-(xvar >> xsimpl >> qexists_tac`1` >>
     fs[eof_def] >> pairarg_tac >> fs[get_file_content_def] >>
     pairarg_tac \\ fs[] \\ rveq \\
     `LENGTH content = pos'` by (fs[] >> rfs[]) >>
     fs[MIN_DEF,liveFS_fsupdate,insert_atI_NIL,bumpFD_def,ALIST_FUPDKEY_unchanged] >>
     rw[DROP_NIL] >- fs[validFD_def,wfFS_fsupdate]
     >- fs[GSYM MAP_DROP,DROP_LENGTH_NIL,insert_atI_NIL] >>
     qmatch_abbrev_tac `IOx _ fs1 ==>> IOx _ fs2 * GC` >>
     `fs1 = fs2` suffices_by xsimpl >>
     unabbrev_all_tac >> cases_on`fs'.numchars` >>
     fs[IO_fs_component_equality,ALIST_FUPDKEY_unchanged,fsupdate_def,LDROP_1,
        wfFS_def,liveFS_def,live_numchars_def]) >>
  NTAC 4 (xlet_auto >- xsimpl) >>
  qmatch_goalsub_abbrev_tac`W8ARRAY bufv buf'' * W8ARRAY iobuff_loc _ *
                            IOx fs_ffi_part fs''` >>
  xapp >> xsimpl >>
  CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
  map_every qexists_tac[`count' + nr`, `fs''`, `SUC n - nr`, `off' + nr`, `pos' + nr`] >>
  unabbrev_all_tac >>
  fs[get_file_content_def, validFD_bumpFD,liveFS_bumpFD,bumpFD_def,get_mode_def] >>
  xsimpl >>
  fs[get_file_content_def, validFD_bumpFD,liveFS_bumpFD,bumpFD_def,get_mode_def,
     ALIST_FUPDKEY_ALOOKUP,INT_OF_NUM_SUBS_2,NUM_def,INT_def] >>
  rw[] >> qexists_tac`SUC x''` >>
  fs[NUM_def,INT_def,MIN_DEF,validFD_def,wfFS_fsupdate,liveFS_fsupdate] >>
  strip_tac
  >-(fs[insert_atI_def,TAKE_APPEND,GSYM MAP_TAKE,TAKE_TAKE_MIN,MIN_DEF] >>
     fs[MAP_TAKE,MAP_DROP,GSYM DROP_DROP] >>
     fs[take_drop_partition,LENGTH_TAKE,LENGTH_DROP,LENGTH_MAP,DROP_APPEND] >>
     qmatch_goalsub_abbrev_tac `l1 ++ l2 ++ l3 = l4` >>
     `l1 = []` by (unabbrev_all_tac >> fs[DROP_NIL,LENGTH_TAKE]) >>
     `l2 = []` by (unabbrev_all_tac >> fs[DROP_NIL,LENGTH_TAKE]) >>
     fs[] >> unabbrev_all_tac >>
     fs[LENGTH_TAKE_EQ_MIN,DROP_DROP_T,MIN_DEF] >> CASE_TAC >> fs[]) >>
  qmatch_abbrev_tac `IOx _ fs1 ==>> IOx _ fs2 * GC` >>
  `fs1 = fs2` suffices_by xsimpl >>
  unabbrev_all_tac >> cases_on`fs'.numchars` >> fs[wfFS_def,liveFS_def,live_numchars_def] >>
  pairarg_tac \\
  fs[IO_fs_component_equality,ALIST_FUPDKEY_unchanged,fsupdate_def,LDROP_1] >>
  fs[ALIST_FUPDKEY_ALOOKUP,ALIST_FUPDKEY_o,ALIST_FUPDKEY_eq] >>
  simp[ALIST_FUPDKEY_unchanged])
  \\ xapp \\ instantiate \\ xsimpl);

Theorem input_spec
  `!fd fdv fs content pos off offv len lenv buf bufv.
    len + off <= LENGTH buf ∧
    INSTREAM fd fdv ∧ NUM off offv ∧ NUM len lenv ∧
    get_file_content fs fd = SOME(content, pos) ⇒
    get_mode fs fd = SOME ReadMode ⇒
    app (p:'ffi ffi_proj) TextIO_input_v [fdv; bufv; offv; lenv]
    (STDIO fs * W8ARRAY bufv buf)
    (POSTv nv. &(NUM (MIN len (LENGTH content - pos)) nv) *
       W8ARRAY bufv (insert_atI (TAKE len (DROP pos (MAP (n2w o ORD) content)))
                                 off buf) *
        STDIO (fsupdate fs fd 0 (MIN (len + pos) (MAX pos (LENGTH content))) content))`
  (rw[STDIO_def]
  \\ xpull
  \\ `fd = 1 ∨ fd = 2 ⇒ pos = LENGTH content`
  by (
    fs[STD_streams_def]
    \\ fs[get_file_content_def]
    \\ pairarg_tac \\ fs[]
    \\ rpt(first_x_assum(qspec_then`fd`mp_tac))
    \\ rw[] \\ fs[]
    \\ metis_tac[SOME_11] )
  \\ `pos = LENGTH content ⇒ MIN (len + pos) (MAX pos (LENGTH content)) = LENGTH content` by simp[MAX_DEF,MIN_DEF]
  \\ simp[STD_streams_fsupdate]
  \\ xapp
  \\ mp_tac(SYM (SPEC_ALL get_file_content_numchars)) \\ rw[]
  \\ mp_tac(get_mode_with_numchars) \\ rw[]
  \\ instantiate \\ xsimpl
  \\ simp[fsupdate_numchars] \\ rw[]
  \\ qexists_tac`THE (LDROP x ll)`
  \\ simp[fsupdate_def]
  \\ fs[get_file_content_def]
  \\ xsimpl);

Theorem extend_array_spec
    `∀arrv arr.
     app (p:'ffi ffi_proj) TextIO_extend_array_v [arrv] (W8ARRAY arrv arr)
       (POSTv v. W8ARRAY v (arr ++ (REPLICATE (LENGTH arr) 0w)))`
    (xcf_with_def "TextIO.extend_array" TextIO_extend_array_v_def
    \\ ntac 5 (xlet_auto >- xsimpl)
    \\ xret \\ xsimpl
    \\ simp[DROP_REPLICATE] );

Theorem inputLine_spec
  `INSTREAM fd fdv ∧ IS_SOME (get_file_content fs fd) ∧ get_mode fs fd = SOME ReadMode
   ⇒
   app (p:'ffi ffi_proj) TextIO_inputLine_v [fdv]
     (STDIO fs)
     (POSTv sov.
       &OPTION_TYPE STRING_TYPE (OPTION_MAP implode (lineFD fs fd)) sov *
       STDIO (lineForwardFD fs fd))`
  (strip_tac \\
  xcf_with_def "TextIO.inputLine" TextIO_inputLine_v_def \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  qpat_abbrev_tac`protect = STDIO fs` \\
  fs[IS_SOME_EXISTS,EXISTS_PROD] \\
  fs[lineFD_def,lineForwardFD_def] \\
  pairarg_tac \\ fs[] \\
  reverse IF_CASES_TAC \\ fs[] >- (
    xfun_spec`inputLine_aux`
      `∀arr arrv.
       0 < LENGTH arr ⇒
       app (p:'ffi ffi_proj) inputLine_aux [arrv;Litv(IntLit 0)]
       (STDIO fs * W8ARRAY arrv arr)
       (POSTv v. &OPTION_TYPE STRING_TYPE NONE v * STDIO fs)`
    >- (
      rw[Abbr`protect`]
      \\ first_x_assum match_mp_tac
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ xif
      \\ instantiate
      \\ xhandle`POSTe e. &EndOfFile_exn e * STDIO fs * W8ARRAY arrv arr`
      >- (
        fs [INSTREAM_def]
        \\ xlet_auto >- xsimpl \\ fs [get_in_def]
        \\ `FD fd sv` by fs [FD_def]
        (* TODO xlet_auto *)
        \\ xlet`POSTe e. &EndOfFile_exn e * STDIO fs * W8ARRAY arrv arr`
        >- (
          fs[STDIO_def] \\ xpull
          \\ xapp
          \\ mp_tac (SPEC_ALL (GSYM get_file_content_numchars))
          \\ mp_tac (get_mode_with_numchars)
          \\ rw[] \\ instantiate
          \\ xsimpl
          \\ imp_res_tac get_file_content_eof \\ fs[]
          \\ rw[bumpFD_0]
          \\ qexists_tac`THE(LTL ll)`
          \\ xsimpl )
        \\ xsimpl )
      \\ xsimpl
      \\ xcases
      \\ fs[EndOfFile_exn_def]
      \\ reverse conj_tac >- (EVAL_TAC \\ fs[])
      \\ `NUM 0 (Litv(IntLit 0))` by EVAL_TAC
      \\ xlet_auto >- xsimpl
      \\ xif
      \\ instantiate
      \\ xcon
      \\ xsimpl
      \\ fs[std_preludeTheory.OPTION_TYPE_def])
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xapp
    \\ xsimpl ) \\
  qabbrev_tac`arrmax = MAX 128 (2 * LENGTH l + 1)` \\
  qmatch_assum_rename_tac`get_file_content fs fd = SOME (content,pos)` \\
  xfun_spec `inputLine_aux`
    `∀pp arr i arrv iv fs.
     arr ≠ [] ∧ i ≤ LENGTH arr ∧ LENGTH arr < arrmax ∧
     NUM i iv ∧ pos ≤ pp ∧ pp ≤ LENGTH content ∧
     get_file_content fs fd = SOME (content,pp) ∧
     get_mode fs fd = SOME ReadMode ∧
     i = pp - pos ∧
     EVERY ($~ o $= #"\n") (TAKE i (DROP pos content)) ∧
     i ≤ LENGTH l ∧ MAP (CHR o w2n) (TAKE i arr) = TAKE i l
     ⇒
     app (p:'ffi ffi_proj) inputLine_aux [arrv; iv]
       (STDIO fs * W8ARRAY arrv arr)
       (POSTv v.
        &(OPTION_TYPE STRING_TYPE (SOME (implode(l ++ "\n"))) v) *
        STDIO (forwardFD fs fd ((LENGTH l - i)+ if NULL r then 0 else 1)))`
  >- (
    qx_gen_tac`pp` \\
    `WF (inv_image ($< LEX $<) (λ(pp,(arr:word8 list)). (arrmax - LENGTH arr, LENGTH content - pp)))`
    by (
      match_mp_tac WF_inv_image \\
      match_mp_tac WF_LEX \\
      simp[] ) \\
    gen_tac \\
    qho_match_abbrev_tac`PC pp arr` \\
    qabbrev_tac`P = λ(pp,arr). PC pp arr` \\
    `∀x. P x` suffices_by simp[FORALL_PROD,Abbr`P`] \\
    qunabbrev_tac`PC` \\
    match_mp_tac(MP_CANON WF_INDUCTION_THM) \\
    asm_exists_tac \\ fs[] \\
    simp[FORALL_PROD,Abbr`P`] \\
    rpt strip_tac \\
    last_x_assum match_mp_tac \\
    xlet_auto >- xsimpl \\
    xlet_auto >- xsimpl \\
    reverse xif >- (
      qmatch_goalsub_rename_tac`W8ARRAY arrv arr` \\
      (* TODO: xlet_auto *)
      xlet`POSTv v. W8ARRAY v (arr ++ REPLICATE (LENGTH arr) 0w) * STDIO fs'`
      >- ( xapp \\ xsimpl )
      \\ xapp
      \\ xsimpl
      \\ instantiate
      \\ xsimpl
      \\ simp[TAKE_APPEND1]
      \\ simp[LEX_DEF]
      \\ Cases_on`LENGTH arr = 0` >- fs[]
      \\ simp[Abbr`arrmax`])
    \\ qmatch_asmsub_rename_tac`MAP _ (TAKE (pp-pos) arr2)`
    \\ qho_match_abbrev_tac`cf_handle _ _ _ _ (POSTv v. post v)`
    \\ reverse (xhandle`POSTve (λv. &(pp < LENGTH content) * post v)
        (λe. &(EndOfFile_exn e ∧ pp = LENGTH content)
             * W8ARRAY arrv arr2 * STDIO fs')`)
    >- (
      xcases \\ xsimpl
      \\ fs[EndOfFile_exn_def]
      \\ reverse conj_tac >- (EVAL_TAC \\ fs[])
      \\ xlet_auto >- xsimpl
      \\ xif
      \\ instantiate
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ xcon
      \\ simp[Abbr`post`]
      \\ fs[TAKE_LENGTH_ID_rwt]
      \\ (SPLITP_NIL_SND_EVERY
          |> SPEC_ALL |> EQ_IMP_RULE |> #2
          |> GEN_ALL |> SIMP_RULE std_ss []
          |> imp_res_tac)
      \\ fs[] \\ rveq
      \\ fs[std_preludeTheory.OPTION_TYPE_def,implode_def,STRING_TYPE_def]
      \\ simp[STDIO_numchars]
      \\ xsimpl
      \\ fs[TAKE_LENGTH_ID_rwt] \\ rveq
      \\ fs[MAP_TAKE,LUPDATE_MAP]
      \\ qpat_x_assum`_ = DROP pos content`(SUBST1_TAC o SYM)
      \\ simp[LIST_EQ_REWRITE,EL_TAKE,EL_LUPDATE,EL_MAP]
      \\ rw[] \\ rw[EL_APPEND_EQN,EL_TAKE,EL_MAP] )
    >- xsimpl
    \\ fs[Abbr`post`]
    \\ fs [INSTREAM_def]
    \\ xlet_auto >- xsimpl \\ fs [get_in_def]
    \\ `FD fd sv` by fs [FD_def]
    \\ xlet `POSTve (λv. &(WORD ((n2w(ORD (EL pp content))):word8) v ∧
                         pp < LENGTH content)
                       * W8ARRAY arrv arr2 * STDIO (forwardFD fs' fd 1))
                    (λe. &(EndOfFile_exn e ∧ pp = LENGTH content)
                       * W8ARRAY arrv arr2 * STDIO fs')`
    >- (
      fs[STDIO_def]
      \\ xpull
      \\ xapp
      \\ mp_tac (SPEC_ALL (Q.SPEC`fs'`(GSYM get_file_content_numchars)))
      \\ mp_tac (Q.SPEC`fs'`(Q.GEN `fs` get_mode_with_numchars))
      \\ rw[]
      \\ asm_exists_tac \\ fs[]
      \\ xsimpl
      \\ imp_res_tac get_file_content_eof \\ fs[]
      \\ simp[bumpFD_numchars,bumpFD_0,bumpFD_forwardFD]
      \\ `pp < LENGTH content ⇒ fd ≠ 1 ∧ fd ≠ 2`
      by (
        fs[STD_streams_def]
        \\ rw[] \\ strip_tac \\ fs[get_file_content_def]
        \\ pairarg_tac \\ fs[] \\ rw[]
        \\ metis_tac[SOME_11,PAIR,prim_recTheory.LESS_REFL,FST,SND])
      \\ simp[STD_streams_forwardFD]
      \\ rw[]
      \\ qexists_tac`THE(LTL ll)`
      \\ xsimpl )
    >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xif
    >- (
      xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ xcon
      >- (
        xsimpl
        \\ fs[std_preludeTheory.OPTION_TYPE_def,implode_def,STRING_TYPE_def,ORD_BOUND]
        \\ qhdtm_x_assum`SPLITP`assume_tac
        \\ qispl_then[`(=)#"\n"`,`pp-pos`,`DROP pos content`]mp_tac SPLITP_TAKE_DROP
        \\ simp[EL_DROP]
        \\ impl_tac >- simp[CHAR_EQ_THM]
        \\ strip_tac \\ rveq \\ unabbrev_all_tac \\ xsimpl
        \\ fs[TAKE_LENGTH_ID_rwt]
        \\ rfs[LENGTH_TAKE,TAKE_LENGTH_ID_rwt]
        \\ simp[DROP_DROP,NULL_EQ,DROP_NIL]
        \\ xsimpl
        \\ qpat_x_assum`_ = _ (DROP pos content)`(SUBST1_TAC o SYM)
        \\ simp[LIST_EQ_REWRITE,EL_TAKE,EL_LUPDATE,EL_MAP]
        \\ rw[] \\ rw[EL_APPEND_EQN,EL_TAKE,EL_MAP])
      \\ xsimpl )
    \\ xlet_auto >- xsimpl
    \\ xapp
    \\ xsimpl
    \\ `pp+1 ≤ LENGTH content` by fs[]
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`pp+1`
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`forwardFD fs' fd 1`
    \\ simp[LEX_DEF]
    \\ xsimpl
    \\ fs[ORD_BOUND]
    \\ first_x_assum(qspec_then`_`kall_tac)
    \\ Cases_on`NULL r`
    >- (
      fs[NULL_EQ]
      \\ imp_res_tac SPLITP_NIL_SND_EVERY
      \\ rveq \\ fs[forwardFD_o,STDIO_numchars]
      \\ xsimpl
      \\ `pp + 1 - pos = (pp - pos) + 1` by fs[]
      \\ pop_assum SUBST_ALL_TAC
      \\ rewrite_tac[TAKE_SUM]
      \\ fs[]
      \\ conj_tac
      >- (
        simp[LIST_EQ_REWRITE,EL_MAP,EL_TAKE,EL_APPEND_EQN,DROP_DROP,EL_LUPDATE,EL_DROP,ORD_BOUND,CHR_ORD]
        \\ rw[] \\ rfs[]
        >- (
          qpat_x_assum`MAP _ _ =  _`mp_tac
          \\ simp[LIST_EQ_REWRITE,EL_MAP,EL_TAKE,EL_DROP] )
        \\ `x = pp - pos` by fs[]
        \\ rw[] )
      \\ unabbrev_all_tac \\ simp[DROP_DROP]
      \\ simp[TAKE1_DROP,CHAR_EQ_THM] \\ xsimpl )
    \\ fs[forwardFD_o,STDIO_numchars]
    \\ xsimpl
    \\ conj_asm1_tac
    >- (
      CCONTR_TAC
      \\ `pp - pos = LENGTH l` by fs[]
      \\ imp_res_tac SPLITP_JOIN
      \\ fs[NULL_EQ]
      \\ `EL (pp - pos) (DROP pos content) = HD r` by ( simp[EL_APPEND2] )
      \\ `pp = LENGTH l + pos` by fs[]
      \\ `EL pp content = HD r` by (
        qpat_x_assum`_ = HD r` (SUBST1_TAC o SYM)
        \\ simp[EL_DROP] )
      \\ imp_res_tac SPLITP_IMP
      \\ rfs[NULL_EQ]
      \\ pop_assum mp_tac
      \\ simp[CHAR_EQ_THM] \\ fs[] )
    \\ conj_tac
    >- (
      qpat_x_assum`MAP _ _ = _`mp_tac
      \\ simp[LIST_EQ_REWRITE,LENGTH_TAKE_EQ,EL_MAP,EL_TAKE,EL_LUPDATE]
      \\ rw[]
      \\ rw[ORD_BOUND,CHR_ORD]
      \\ imp_res_tac SPLITP_JOIN
      \\ `EL (pp - pos) l = EL (pp - pos) (DROP pos content)` by simp[EL_APPEND_EQN]
      \\ pop_assum SUBST1_TAC
      \\ simp[EL_DROP] )
    \\ `pp + 1 - pos = (pp - pos) + 1` by fs[]
    \\ pop_assum SUBST_ALL_TAC
    \\ rewrite_tac[TAKE_SUM]
    \\ simp[]
    \\ simp[TAKE1_DROP,EL_DROP,CHAR_EQ_THM]
    \\ unabbrev_all_tac \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ xsimpl
  \\ simp[Abbr`arrmax`,Abbr`protect`]
  \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
  \\ qexists_tac`pos` \\ simp[]
  \\ instantiate
  \\ xsimpl
  \\ EVAL_TAC);

Theorem inputLines_spec
  `!fd fdv fs. INSTREAM fd fdv ∧
   get_file_content fs fd = SOME (content,pos) ∧
   get_mode fs fd = SOME ReadMode
   ⇒
   app (p:'ffi ffi_proj) TextIO_inputLines_v [fdv]
     (STDIO fs)
     (POSTv fcv.
       &LIST_TYPE STRING_TYPE
         (MAP (\x. strcat (implode x) (implode "\n"))
            (splitlines (DROP pos content))) fcv *
       STDIO (fastForwardFD fs fd))`
  (Induct_on`splitlines (DROP pos content)` \\ rw[]
  >- (
    qpat_x_assum`[] = _`(assume_tac o SYM) \\ fs[DROP_NIL]
    \\ `LENGTH content - pos = 0` by simp[]
    \\ pop_assum SUBST1_TAC
    \\ `DROP pos content = []` by fs[DROP_NIL]
    \\ xcf_with_def "TextIO.inputLines" TextIO_inputLines_v_def
    \\ `IS_SOME (get_file_content fs fd)` by fs[IS_SOME_EXISTS]
    \\ xlet_auto >- xsimpl
    \\ rfs[std_preludeTheory.OPTION_TYPE_def,lineFD_def]
    \\ xmatch
    \\ xcon
    \\ simp[lineForwardFD_def,fastForwardFD_0]
    \\ xsimpl
    \\ fs[LIST_TYPE_def])
  \\ qpat_x_assum`_::_ = _`(assume_tac o SYM) \\ fs[]
  \\ xcf_with_def "TextIO.inputLines" TextIO_inputLines_v_def
  \\ `IS_SOME (get_file_content fs fd)` by fs[IS_SOME_EXISTS]
  \\ xlet_auto >- xsimpl
  \\ rfs[lineFD_def]
  \\ imp_res_tac splitlines_next
  \\ rveq
  \\ `pos < LENGTH content`
  by ( CCONTR_TAC \\ fs[NOT_LESS,GSYM GREATER_EQ,GSYM DROP_NIL] )
  \\ fs[DROP_DROP_T]
  \\ pairarg_tac \\ fs[implode_def,STRING_TYPE_def,std_preludeTheory.OPTION_TYPE_def] \\ rveq
  \\ xmatch
  \\ fs[lineForwardFD_def]
  \\ imp_res_tac splitlines_CONS_FST_SPLITP \\ rfs[] \\ rveq
  \\ qmatch_goalsub_abbrev_tac`forwardFD fs fd n`
  \\ first_x_assum(qspecl_then[`pos+n`,`content`]mp_tac)
  \\ impl_keep_tac
  >- (
    simp[Abbr`n`]
    \\ rw[ADD1]
    \\ fs[NULL_EQ]
    \\ imp_res_tac SPLITP_NIL_SND_EVERY
    \\ rveq
    \\ simp[DROP_LENGTH_TOO_LONG] )
  \\  disch_then drule
  \\ disch_then(qspec_then`forwardFD fs fd n`mp_tac)
  \\ simp[]
  \\ strip_tac \\ fs[Abbr`n`,NULL_EQ]
  \\ xlet_auto >- xsimpl
  \\ xcon
  \\ xsimpl
  \\ simp[forwardFD_o,STDIO_numchars,LIST_TYPE_def]
  \\ fs[strcat_thm,implode_def]
  \\ qmatch_goalsub_abbrev_tac`forwardFD fs fd n`
  \\ `n ≤ LENGTH content - pos` suffices_by (
    simp[fastForwardFD_forwardFD] \\ xsimpl)
  \\ imp_res_tac IS_PREFIX_LENGTH
  \\ fs[] \\ rw[Abbr`n`] \\ fs[]
  \\ Cases_on`LENGTH h = LENGTH content - pos` \\ fs[]
  \\ imp_res_tac SPLITP_JOIN
  \\ pop_assum(mp_tac o Q.AP_TERM`LENGTH`) \\ simp[]
  \\ Cases_on`LENGTH r = 0` \\ simp[] \\ fs[] );

Theorem inputLinesFrom_spec
  `FILENAME f fv /\ hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) TextIO_inputLinesFrom_v
     [fv]
     (STDIO fs)
     (POSTv sv. &OPTION_TYPE (LIST_TYPE STRING_TYPE)
            (if inFS_fname fs (File f) then
               SOME(all_lines fs (File f))
             else NONE) sv
             * STDIO fs)`
  (xcf_with_def "TextIO.inputLinesFrom" TextIO_inputLinesFrom_v_def
  \\ reverse(xhandle`POSTve
       (λv. &OPTION_TYPE (LIST_TYPE STRING_TYPE)
         (if inFS_fname fs (File f)
          then SOME(all_lines fs (File f))
          else NONE) v * STDIO fs)
       (λe. &(BadFileName_exn e ∧ ¬inFS_fname fs (File f)) * STDIO fs)`)
  >- (xcases \\ fs[BadFileName_exn_def]
      \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
      \\ xcon \\ xsimpl \\ fs[std_preludeTheory.OPTION_TYPE_def])
  >- xsimpl
  \\ `CARD (set (MAP FST fs.infds)) < fs.maxFD` by fs[]
  \\ reverse(Cases_on`STD_streams fs`)
  >- ( fs[STDIO_def] \\ xpull )
  \\ xlet_auto_spec (SOME (SPEC_ALL openIn_STDIO_spec))
  >- (
    xsimpl
    \\ fs[nextFD_numchars,openFileFS_fupd_numchars,inFS_fname_numchars,GSYM validFD_numchars]
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`ll` \\ xsimpl )
  >- (
    xsimpl
    \\ rw[inFS_fname_numchars]
    \\ qexists_tac`ll` \\ xsimpl )
  \\ drule (GEN_ALL ALOOKUP_inFS_fname_openFileFS_nextFD)
  \\ imp_res_tac nextFD_ltX
  \\ disch_then(qspec_then`0`mp_tac) \\ rw[]
  \\ qmatch_assum_abbrev_tac`validFD fd fso`
  \\ `∃c. get_file_content fso fd = SOME (c,0)`
  by (
    fs[get_file_content_def,validFD_def,Abbr`fso`,openFileFS_files]
    \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS \\ fs[] )
  \\ `get_mode fso fd = SOME ReadMode`
  by ( simp[Abbr`fso`, openFileFS_def, get_mode_def] )
  \\ xlet_auto >- xsimpl
  \\ qmatch_goalsub_abbrev_tac`STDIO fsob`
  \\ rename1 `INSTREAM fd fdv`
  \\ qspecl_then[`fd`,`fsob`,`fdv`]mp_tac closeIn_STDIO_spec
  \\ impl_tac >- (
    fs[STD_streams_def, Abbr`fsob`, Abbr`fso`]
    \\ `¬(fd = 0 ∨ fd = 1 ∨ fd = 2)` suffices_by fs[]
    \\ metis_tac[nextFD_NOT_MEM,ALOOKUP_MEM] )
  \\ strip_tac
  \\ `validFileFD fd fso.infds`
  by (
    simp[validFileFD_def]
    \\ imp_res_tac ALOOKUP_inFS_fname_openFileFS_nextFD
    \\ rfs[]
    \\ first_x_assum(qspecl_then[`0`,`ReadMode`]mp_tac)
    \\ simp_tac(srw_ss())[Abbr`fso`] )
  \\ `validFileFD fd fsob.infds`
  by ( simp[Abbr`fsob`, validFileFD_fastForwardFD] )
  \\ xlet_auto_spec(SOME closeIn_STDIO_spec)
  >- (
    xsimpl
    \\ simp[Abbr`fsob`, Abbr`fso`]
    \\ imp_res_tac STD_streams_nextFD
    \\ rfs[])
  >- xsimpl
  \\ reverse xcon \\ xsimpl
  \\ fs[]
  \\ fs[all_lines_def,lines_of_def]
  \\ fs[get_file_content_def]
  \\ pairarg_tac \\ fs[]
  \\ fs[Abbr`fso`,openFileFS_files]
  \\ rveq \\ fs[]
  \\ qmatch_goalsub_abbrev_tac`STDIO fs'`
  \\ first_x_assum(qspec_then`ReadMode`mp_tac) \\ strip_tac \\ fs[]
  \\ `fs' = fs` suffices_by ( rw[std_preludeTheory.OPTION_TYPE_def] \\ xsimpl)
  \\ unabbrev_all_tac
  \\ simp[fastForwardFD_def,A_DELKEY_ALIST_FUPDKEY,o_DEF,
          libTheory.the_def, openFileFS_numchars,
          IO_fs_component_equality,openFileFS_files]);

val inputLinesFrom_def = Define `
  inputLinesFrom f =
    (\fs. (Success (if inFS_fname fs (File f) then
                      SOME(all_lines fs (File f))
                    else NONE), fs))`;

Theorem EvalM_inputLinesFrom
  `Eval env exp (FILENAME f) /\
    (nsLookup env.v (Long "TextIO" (Short "inputLinesFrom")) =
       SOME TextIO_inputLinesFrom_v) ==>
    EvalM F env st (App Opapp [Var (Long "TextIO" (Short "inputLinesFrom")); exp])
      (MONAD (OPTION_TYPE (LIST_TYPE STRING_TYPE)) exc_ty (inputLinesFrom f))
      (MONAD_IO,p:'ffi ffi_proj)`
  (ho_match_mp_tac EvalM_from_app
  \\ conj_tac >- rw [inputLinesFrom_def]
  \\ rw [MONAD_IO_def]
  \\ xpull
  \\ fs [SEP_CLAUSES]
  \\ match_mp_tac (app_weaken |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO])
  \\ drule (GEN_ALL inputLinesFrom_spec)
  \\ disch_then (qspecl_then [`p`,`s`] assume_tac)
  \\ rfs [inputLinesFrom_def]
  \\ asm_exists_tac \\ fs []
  \\ xsimpl);

Theorem inputAll_spec
  `INSTREAM fd fdv ∧
   get_file_content fs fd = SOME (content,pos) ⇒
   get_mode fs fd = SOME ReadMode ⇒
   app (p:'ffi ffi_proj) TextIO_inputAll_v [fdv]
   (STDIO fs)
   (POSTv v.
     &STRING_TYPE (implode (DROP pos content)) v *
     STDIO (fastForwardFD fs fd))`
  (xcf_with_def "TextIO.inputAll" TextIO_inputAll_v_def \\
  reverse(Cases_on`pos ≤ LENGTH content`)
  >- (
    xfun_spec `inputAll_aux`
    `∀iv arr arrv. NUM 0 iv ∧ arr ≠ [] ⇒
     app (p:'ffi ffi_proj) inputAll_aux [arrv; iv]
       (STDIO fs * W8ARRAY arrv arr)
       (POSTv v. &STRING_TYPE (strlit"") v * STDIO fs)`
    >- (
      rw[] \\
      first_x_assum match_mp_tac \\
      xlet_auto >- xsimpl \\
      xlet_auto >- xsimpl \\
      xif \\
      instantiate \\
      strip_tac \\
      xlet_auto >- xsimpl \\
      xlet_auto_spec(SOME input_spec)
      >- xsimpl \\
      xlet_auto >- xsimpl \\
      xif \\ instantiate \\
      xapp \\
      simp[DROP_LENGTH_TOO_LONG,insert_atI_NIL] \\
      xsimpl \\ instantiate \\
      simp[STRING_TYPE_def] \\
      simp[MAX_DEF] \\
      simp[fsupdate_unchanged] \\
      xsimpl )
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xapp \\ xsimpl
    \\ simp[DROP_LENGTH_TOO_LONG,implode_def]
    \\ simp[fastForwardFD_0]
    \\ xsimpl
    \\ EVAL_TAC )
  \\ qabbrev_tac`arrmax = SUC (MAX 127 (2 * (LENGTH content - pos)))` \\
  xfun_spec `inputAll_aux`
    `∀i arr arrv iv fs.
     arr ≠ [] ∧ i ≤ LENGTH arr ∧ LENGTH arr < arrmax ∧
     NUM i iv ∧ pos + i ≤ LENGTH content ∧
     get_file_content fs fd = SOME (content,pos+i) ∧
     get_mode fs fd = SOME ReadMode ∧
     MAP (CHR o w2n) (TAKE i arr) = TAKE i (DROP pos content)
     ⇒
     app (p:'ffi ffi_proj) inputAll_aux [arrv; iv]
       (STDIO fs * W8ARRAY arrv arr)
       (POSTv v.
        &(STRING_TYPE (implode(DROP pos content)) v) *
        STDIO (fastForwardFD fs fd))`
  >- (
    qx_gen_tac`i` \\
    `WF (inv_image ($< LEX $<) (λ(i,(arr:word8 list)). (arrmax - LENGTH arr, LENGTH content - i)))`
    by (
      match_mp_tac WF_inv_image \\
      match_mp_tac WF_LEX \\
      simp[] ) \\
    gen_tac \\
    qho_match_abbrev_tac`PC i arr` \\
    qabbrev_tac`P = λ(i,arr). PC i arr` \\
    `∀x. P x` suffices_by simp[FORALL_PROD,Abbr`P`] \\
    qunabbrev_tac`PC` \\
    match_mp_tac(MP_CANON WF_INDUCTION_THM) \\
    asm_exists_tac \\ fs[] \\
    simp[FORALL_PROD,Abbr`P`] \\
    rpt strip_tac \\
    last_x_assum match_mp_tac \\
    xlet_auto >- xsimpl \\
    xlet_auto >- xsimpl \\
    xif \\ fs[]
    >- (
      xlet_auto >- xsimpl
      \\ xlet_auto_spec(SOME input_spec)
      >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ xif \\ fs[] \\ rfs[]
      >- (
        pop_assum mp_tac \\ rw[] \\ fs[]
        \\ xapp
        \\ xsimpl
        \\ simp[DROP_LENGTH_TOO_LONG,insert_atI_NIL]
        \\ instantiate
        \\ simp[TAKE_LENGTH_TOO_LONG,implode_def,MAX_DEF,STRING_TYPE_def]
        \\ simp[fsupdate_unchanged,fastForwardFD_0]
        \\ xsimpl )
      \\ xlet_auto >- xsimpl
      \\ simp[MAX_DEF]
      \\ xapp
      \\ xsimpl
      \\ simp[LENGTH_insert_atI,LENGTH_TAKE_EQ]
      \\ qmatch_goalsub_abbrev_tac`STDIO fs2`
      \\ CONV_TAC SWAP_EXISTS_CONV
      \\ qexists_tac`fs2` \\ xsimpl
      \\ first_assum(mp_then Any mp_tac get_file_content_fsupdate)
      \\ qmatch_asmsub_abbrev_tac`fs2 = fsupdate fs' fd 0 i content`
      \\ disch_then(qspecl_then[`0`,`i`,`content`]mp_tac) \\ rw[]
      \\ qmatch_assum_rename_tac`MAP _ (TAKE j arr) = TAKE j _`
      \\ simp[LEX_DEF]
      \\ `i ≤ LENGTH content` by rw[Abbr`i`]
      \\ `j + pos < i` by rw[Abbr`i`]
      \\ `i ≤ pos + LENGTH arr` by rw[Abbr`i`]
      \\ `NUM (i-pos) nv2` by ( rw[Abbr`i`] \\ fs[] )
      \\ qexists_tac`i - pos`
      \\ simp[]
      \\ `fs2 = forwardFD fs' fd (i - pos - j)`
      by (
        simp[Abbr`fs2`,forwardFD_def,fsupdate_def]
        \\ fs[get_file_content_def]
        \\ rpt (pairarg_tac \\ fs[])
        \\ fs[IO_fs_component_equality,ALIST_FUPDKEY_unchanged,ALIST_FUPDKEY_eq] )
      \\ qunabbrev_tac`fs2` \\ pop_assum SUBST_ALL_TAC
      \\ simp[fastForwardFD_forwardFD]
      \\ xsimpl
      \\ conj_tac
      >- (
        rewrite_tac[GSYM LENGTH_NIL]
        \\ asm_simp_tac(std_ss++ARITH_ss)[LENGTH_insert_atI,LENGTH_TAKE_EQ,LENGTH_DROP,LENGTH_MAP] )
      \\ qpat_x_assum`_ = TAKE _ _`mp_tac
      \\ simp[LIST_EQ_REWRITE,LENGTH_TAKE_EQ,EL_MAP,EL_TAKE,EL_DROP,insert_atI_def,EL_APPEND_EQN]
      \\ rw[]
      \\ rw[ORD_BOUND,CHR_ORD] )
    \\ xlet_auto >- xsimpl
    \\ xapp
    \\ simp[Abbr`arrmax`]
    \\ xsimpl
    \\ instantiate
    \\ simp[LEX_DEF,TAKE_APPEND]
    \\ xsimpl
    \\ fs[MAX_DEF]
    \\ CCONTR_TAC \\ fs[])
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ first_x_assum(qspecl_then[`0`,`REPLICATE 127 0w`]mp_tac)
  \\ simp[NUM_def,INT_def]
  \\ disch_then(first_assum o mp_then Any mp_tac)
  \\ simp[Abbr`arrmax`,MAX_DEF,Once REPLICATE_compute]
  \\ strip_tac
  \\ xapp \\ xsimpl );

Theorem print_list_spec
  `∀ls lv fs out. LIST_TYPE STRING_TYPE ls lv ⇒
   app (p:'ffi ffi_proj) TextIO_print_list_v [lv]
     (STDIO fs)
     (POSTv v. &UNIT_TYPE () v * STDIO (add_stdout fs (concat ls)))`
  (Induct \\ rw[LIST_TYPE_def]
  \\ xcf_with_def "TextIO.print_list" TextIO_print_list_v_def
  \\ (reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull))
  \\ xmatch
  >- (xcon \\ fs[STD_streams_stdout,add_stdo_nil] \\ xsimpl)
  \\ rename1`STRING_TYPE s sv`
  \\ xlet_auto >- xsimpl
  \\ xapp \\ xsimpl
  \\ imp_res_tac STD_streams_stdout
  \\ imp_res_tac add_stdo_o
  \\ simp[concat_cons]
  \\ map_every qexists_tac [`emp`,`add_stdout fs s`]
  \\ xsimpl);

val _ = export_theory();
