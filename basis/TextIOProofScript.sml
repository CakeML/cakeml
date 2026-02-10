(*
  Proofs about the code in the TextIO module.
*)
Theory TextIOProof
Ancestors
  cfMain cfLetAuto ml_monadBase ml_translator ml_monad_translator
  mlstring fsFFI fsFFIProps Word8Prog Word8ArrayProof TextIOProg
  MarshallingProg Marshalling integer int_arith
Libs
  preamble ml_translatorLib ml_progLib cfLib basisFunctionsLib
  cfMonadLib

val _ = temp_delsimps ["NORMEQ_CONV", "TAKE_LENGTH_ID_rwt2", "TAKE_LENGTH_ID_rwt2"];

val _ = translation_extends "TextIOProg";
val _ = preamble.option_monadsyntax.temp_add_option_monadsyntax();

(* heap predicate for the file-system state *)

Definition IOFS_iobuff_def:
  IOFS_iobuff =
    SEP_EXISTS v. W8ARRAY iobuff_loc v * cond (LENGTH v >= 2052)
End

Definition IOFS_def:
  IOFS fs = IOx (fs_ffi_part) fs * IOFS_iobuff * &wfFS fs
End

(*Used for read_into where the target buffer is specified*)
Definition IOFS_WO_iobuff_def:
  IOFS_WO_iobuff fs = IOx (fs_ffi_part) fs * &wfFS fs
End

Theorem UNIQUE_IOFS:
!s. VALID_HEAP s ==> !fs1 fs2 H1 H2. (IOFS fs1 * H1) s /\
                                      (IOFS fs2 * H2) s ==> fs1 = fs2
Proof
  rw[IOFS_def,cfHeapsBaseTheory.IOx_def, fs_ffi_part_def,
     GSYM STAR_ASSOC,encode_def] >>
  IMP_RES_TAC FRAME_UNIQUE_IO >>
  fs[IO_fs_component_equality]
QED

Theorem IOFS_FFI_part_hprop:
  FFI_part_hprop (IOFS fs)
Proof
  rw [IOFS_def,
      cfHeapsBaseTheory.IO_def, cfHeapsBaseTheory.IOx_def,
      fs_ffi_part_def, cfMainTheory.FFI_part_hprop_def,
    set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
    cfHeapsBaseTheory.W8ARRAY_def,IOFS_iobuff_def,
    cfHeapsBaseTheory.cell_def]
  \\ fs[set_sepTheory.one_STAR,STAR_def]
  \\ imp_res_tac SPLIT_SUBSET >> fs[SUBSET_DEF]
  \\ metis_tac[]
QED

Theorem IOFS_iobuff_HPROP_INJ[hprop_inj]:
  !fs1 fs2. HPROP_INJ (IOFS fs1) (IOFS fs2) (fs2 = fs1)
Proof
  rw[HPROP_INJ_def, IOFS_def, GSYM STAR_ASSOC, SEP_CLAUSES, SEP_EXISTS_THM,
     HCOND_EXTRACT] >>
  fs[IOFS_def,cfHeapsBaseTheory.IOx_def, fs_ffi_part_def] >>
  EQ_TAC >> rpt DISCH_TAC >> IMP_RES_TAC FRAME_UNIQUE_IO >> fs[]
QED

(* "end-user" property *)
(* abstracts away the lazy list and ensure that standard streams are opened on
 * their respective standard fds at the right position *)

Definition STDIO_def:
 STDIO fs = (SEP_EXISTS ll. IOFS (fs with numchars := ll)) *
   &STD_streams fs
End

Theorem STDIO_STD_streams:
  STDIO fs = STDIO fs * &STD_streams fs
Proof
  Cases_on ‘STD_streams fs’ \\ simp[STDIO_def, SEP_CLAUSES]
QED

Theorem STDIO_consistentFS:
  STDIO fs = STDIO fs * &(consistentFS fs)
Proof
  Cases_on ‘consistentFS fs’ \\ simp [SEP_CLAUSES]
  \\ simp [FUN_EQ_THM, SEP_F_def] \\ rpt strip_tac
  \\ gvs [STDIO_def, IOFS_def, wfFS_def, cond_def, STAR_def, SEP_EXISTS_THM,
          consistentFS_def]
  \\ res_tac
QED

(* Used by the monadic translator *)
Definition MONAD_IO_def:
  MONAD_IO fs = STDIO fs * &hasFreeFD fs
End

Theorem STDIO_numchars:
  STDIO (fs with numchars := x) = STDIO fs
Proof
  rw[STDIO_def,GSYM STD_streams_numchars]
QED

Theorem STDIO_bumpFD[simp]:
  STDIO (bumpFD fd fs n) = STDIO (forwardFD fs fd n)
Proof
  rw[bumpFD_forwardFD,STDIO_numchars]
QED

Theorem UNIQUE_STDIO:
  !s. VALID_HEAP s ==> !fs1 fs2 H1 H2. (STDIO fs1 * H1) s /\
                                      (STDIO fs2 * H2) s ==>
              (fs1.infds = fs2.infds /\ fs1.files = fs2.files /\ fs1.maxFD = fs2.maxFD /\ fs1.inode_tbl = fs2.inode_tbl)
Proof
  rw[STDIO_def,STD_streams_def,SEP_CLAUSES,SEP_EXISTS_THM,STAR_COMM,STAR_ASSOC,cond_STAR] >>
  fs[Once STAR_COMM] >>
  imp_res_tac UNIQUE_IOFS >>
  cases_on`fs1` >> cases_on`fs2` >> fs[recordtype_IO_fs_seldef_numchars_fupd_def]
QED

(* weak injection theorem *)
Theorem STDIO_HPROP_INJ[hprop_inj]:
  HPROP_INJ (STDIO fs1) (STDIO fs2)
           (fs1.infds = fs2.infds /\ fs1.files = fs2.files /\ fs1.maxFD = fs2.maxFD /\ fs1.inode_tbl = fs2.inode_tbl)
Proof
  rw[HPROP_INJ_def, GSYM STAR_ASSOC, SEP_CLAUSES, SEP_EXISTS_THM,
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
     cases_on`fs1` >> cases_on`fs2` >> fs[recordtype_IO_fs_seldef_numchars_fupd_def] >>
     metis_tac[]
     ) >>
  fs[STDIO_def,STD_streams_def,STAR_def,SEP_EXISTS,cond_def] >>
  qmatch_assum_rename_tac`IOFS (fs1 with numchars := ll) u1` >>
  qmatch_assum_rename_tac`SPLIT u0 (u1, _)` >>
  qmatch_assum_rename_tac`SPLIT s (u0, v0)` >>
  qexists_tac`u0` >> qexists_tac`v0` >> fs[] >>
  qexists_tac`u1` >> fs[PULL_EXISTS] >> qexists_tac`ll` >> fs[] >>
  cases_on`fs1` >> cases_on`fs2` >> fs[recordtype_IO_fs_seldef_numchars_fupd_def] >>
  metis_tac[]
QED

(* refinement invariant for filenames *)
Definition FILENAME_def:
  FILENAME s sv =
    (STRING_TYPE s sv ∧
     ¬MEM (CHR 0) (explode s) ∧
     strlen s < 256 * 256)
End

val filename_tac = metis_tac[FILENAME_def,EqualityType_NUM_BOOL,EqualityType_def];

Theorem FILENAME_UNICITY_R[xlet_auto_match]:
  !f fv fv'. FILENAME f fv ==> (FILENAME f fv' <=> fv' = fv)
Proof
  filename_tac
QED

Theorem FILENAME_UNICITY_L[xlet_auto_match]:
  !f f' fv. FILENAME f fv ==> (FILENAME f' fv <=> f' = f)
Proof
  filename_tac
QED

Theorem FILENAME_STRING_UNICITY_R[xlet_auto_match]:
  !f fv fv'. FILENAME f fv ==> (STRING_TYPE f fv' <=> fv' = fv)
Proof
  filename_tac
QED

Theorem FILENAME_STRING_UNICITY_L[xlet_auto_match]:
  !f f' fv. FILENAME f fv ==> (STRING_TYPE f' fv <=> f' = f)
Proof
  filename_tac
QED

Theorem STRING_FILENAME_UNICITY_R[xlet_auto_match]:
  !f fv fv'. STRING_TYPE f fv ==>
    (FILENAME f fv' <=> fv' = fv /\ ¬MEM #"\^@" (explode f) /\ strlen f < 256 * 256)
Proof
  filename_tac
QED

Theorem STRING_FILENAME_UNICITY_L[xlet_auto_match]:
  !f f' fv. STRING_TYPE f fv ==>
    (FILENAME f' fv <=> f' = f /\ ¬MEM #"\^@" (explode f) /\ strlen f < 256 * 256)
Proof
  filename_tac
QED

(* exception refinement invariant lemmas *)

Theorem BadFileName_UNICITY[xlet_auto_match]:
!v1 v2. BadFileName_exn v1 ==> (BadFileName_exn v2 <=> v2 = v1)
Proof
  fs[BadFileName_exn_def]
QED

Theorem InvalidFD_UNICITY[xlet_auto_match]:
  !v1 v2. InvalidFD_exn v1 ==> (InvalidFD_exn v2 <=> v2 = v1)
Proof
  fs[InvalidFD_exn_def]
QED

Theorem EndOfFile_UNICITY[xlet_auto_match]:
  !v1 v2. EndOfFile_exn v1 ==> (EndOfFile_exn v2 <=> v2 = v1)
Proof
  fs[EndOfFile_exn_def]
QED

Theorem IllegalArgument_UNICITY[xlet_auto_match]:
  !v1 v2. IllegalArgument_exn v1 ==> (IllegalArgument_exn v2 <=> v2 = v1)
Proof
  fs[IllegalArgument_exn_def]
QED

(* convenient functions for standard output/error
 * n.b. numchars is ignored *)

Definition stdo_def:
  stdo fd name fs out =
    (ALOOKUP fs.infds fd = SOME(UStream(implode name),WriteMode,strlen out) /\
     ALOOKUP fs.inode_tbl (UStream(implode name)) = SOME (explode out))
End

Overload stdout = ``stdo 1 "stdout"``;
Overload stderr = ``stdo 2 "stderr"``;

Theorem stdo_UNICITY_R[xlet_auto_match]:
 !fd name fs out out'. stdo fd name fs out ==> (stdo fd name fs out' <=> out = out')
Proof
rw[stdo_def] >> EQ_TAC >> rw[explode_11]
QED

Definition up_stdo_def:
  up_stdo fd fs out = fsupdate fs fd 0 (strlen out) (explode out)
End
Overload up_stdout = ``up_stdo 1``;
Overload up_stderr = ``up_stdo 2``;

Theorem stdo_numchars:
   stdo fd name (fs with numchars := l) out ⇔ stdo fd name fs out
Proof
  rw[stdo_def]
QED

Theorem up_stdo_numchars[simp]:
   (up_stdo fd fs x).numchars = fs.numchars
Proof
  rw[up_stdo_def,fsupdate_def]
  \\ CASE_TAC \\ CASE_TAC \\ rw[]
QED

Theorem fsupdate_files[simp]:
  (fsupdate fs fd k pos c).files = fs.files
Proof
 fs[fsupdate_def] >> NTAC 2 CASE_TAC >>fs[]
QED

Theorem up_stdo_files[simp]:
  (up_stdo fd fs x).files = fs.files
Proof
 fs[up_stdo_def,fsupdate_def] >> NTAC 2 CASE_TAC >>fs[]
QED

Theorem up_stdo_maxFD[simp]:
   (up_stdo fd fs x).maxFD = fs.maxFD
Proof
  rw[up_stdo_def,fsupdate_def]
  \\ CASE_TAC \\ CASE_TAC \\ rw[]
QED

Theorem up_stdo_with_numchars:
   up_stdo fd (fs with numchars := ns) x =
   up_stdo fd fs x with numchars := ns
Proof
  rw[up_stdo_def,fsupdate_numchars]
QED

Definition add_stdo_def:
  add_stdo fd nm fs out = up_stdo fd fs ((@init. stdo fd nm fs init) ^ out)
End
Overload add_stdout = ``add_stdo 1 "stdout"``;
Overload add_stderr = ``add_stdo 2 "stderr"``;


Theorem stdo_add_stdo:
   stdo fd nm fs init ⇒ stdo fd nm (add_stdo fd nm fs out) (strcat init out)
Proof
  rw[add_stdo_def]
  \\ SELECT_ELIM_TAC \\ rw[] >- metis_tac[]
  \\ imp_res_tac stdo_UNICITY_R \\ rveq
  \\ fs[up_stdo_def,stdo_def,fsupdate_def,AFUPDKEY_ALOOKUP]
QED

Theorem up_stdo_unchanged:
  !fs out. stdo fd nm fs out ==> up_stdo fd fs out = fs
Proof
fs[up_stdo_def,stdo_def,fsupdate_unchanged,get_file_content_def,PULL_EXISTS]
QED

Theorem stdo_up_stdo:
  !fs out out'. stdo fd nm fs out ==> stdo fd nm (up_stdo fd fs out') out'
Proof
 rw[up_stdo_def,stdo_def,fsupdate_def,AFUPDKEY_ALOOKUP,PULL_EXISTS]
 \\ rw[]
QED

Theorem add_stdo_nil:
   stdo fd nm fs out ⇒ add_stdo fd nm fs (strlit "") = fs
Proof
  rw[add_stdo_def]
  \\ SELECT_ELIM_TAC
  \\ metis_tac[up_stdo_unchanged]
QED

Theorem add_stdout_nil:
  STD_streams fs ⇒ add_stdout fs «» = fs
Proof
  strip_tac
  \\ irule add_stdo_nil
  \\ fs [STD_streams_def, stdo_def, implode_def]
  \\ qrefine ‘implode x’ \\ simp []
QED

Theorem add_stdo_o:
   stdo fd nm fs out ⇒
   add_stdo fd nm (add_stdo fd nm fs x1) x2 = add_stdo fd nm fs (x1 ^ x2)
Proof
  rw[add_stdo_def]
  \\ SELECT_ELIM_TAC \\ rw[] >- metis_tac[]
  \\ SELECT_ELIM_TAC \\ rw[] >- metis_tac[stdo_up_stdo]
  \\ imp_res_tac stdo_UNICITY_R \\ rveq
  \\ rename1`stdo _ _ (up_stdo _ _ _) l`
  \\ `l = out ^ x1` by metis_tac[stdo_UNICITY_R,stdo_up_stdo]
  \\ rveq \\ fs[up_stdo_def]
QED

Theorem add_stdo_numchars[simp]:
   (add_stdo fd nm fs x).numchars = fs.numchars
Proof
  rw[add_stdo_def]
QED

Theorem add_stdo_maxFD[simp]:
   (add_stdo fd nm fs x).maxFD = fs.maxFD
Proof
  rw[add_stdo_def]
QED

Theorem add_stdo_with_numchars:
   add_stdo fd nm (fs with numchars := ns) x =
   add_stdo fd nm fs x with numchars := ns
Proof
  rw[add_stdo_def,stdo_numchars,up_stdo_with_numchars]
QED

Theorem up_stdo_MAP_FST_infds[simp]:
   MAP FST (up_stdo fd fs out).infds = MAP FST fs.infds
Proof
  rw[up_stdo_def]
QED

Theorem add_stdo_MAP_FST_infds[simp]:
   MAP FST (add_stdo fd nm fs out).infds = MAP FST fs.infds
Proof
  rw[add_stdo_def]
QED

Theorem up_stdo_MAP_FST_files[simp]:
   MAP FST (up_stdo fd fs out).files = MAP FST fs.files
Proof
  rw[up_stdo_def]
QED

Theorem up_stdo_MAP_FST_inode_tbl[simp]:
   MAP FST (up_stdo fd fs out).inode_tbl = MAP FST fs.inode_tbl
Proof
  rw[up_stdo_def]
QED

Theorem add_stdo_MAP_FST_inode_tbl[simp]:
   MAP FST (add_stdo fd nm fs out).inode_tbl = MAP FST fs.inode_tbl
Proof
  rw[add_stdo_def]
QED

Theorem inFS_fname_add_stdo[simp]:
   inFS_fname (add_stdo fd nm fs out) = inFS_fname fs
Proof
  rw[inFS_fname_def,FUN_EQ_THM] >> EVAL_TAC >> EVERY_CASE_TAC >> rw[]
QED

Theorem STD_streams_stdout:
   STD_streams fs ⇒ ∃out. stdout fs out
Proof
  rw[STD_streams_def,stdo_def,implode_def] \\ rw[]
  \\ metis_tac[explode_implode,strlen_implode]
QED

Theorem STD_streams_stderr:
   STD_streams fs ⇒ ∃out. stderr fs out
Proof
  rw[STD_streams_def,stdo_def,implode_def] \\ rw[]
  \\ metis_tac[explode_implode,strlen_implode]
QED

Theorem STD_streams_add_stdout:
   STD_streams fs ⇒ STD_streams (add_stdout fs out)
Proof
  rw[]
  \\ imp_res_tac STD_streams_stdout
  \\ rw[add_stdo_def]
  \\ SELECT_ELIM_TAC
  \\ rw[] >- metis_tac[]
  \\ rw[up_stdo_def]
  \\ match_mp_tac STD_streams_fsupdate \\ rw[]
QED

Theorem STD_streams_add_stderr:
   STD_streams fs ⇒ STD_streams (add_stderr fs out)
Proof
  rw[]
  \\ imp_res_tac STD_streams_stderr
  \\ rw[add_stdo_def]
  \\ SELECT_ELIM_TAC
  \\ rw[] >- metis_tac[]
  \\ rw[up_stdo_def]
  \\ match_mp_tac STD_streams_fsupdate \\ rw[]
QED

Theorem fsupdate_add_stdout_implode:
  STD_streams fs ∧ get_file_content fs 1 = SOME (content,pos) ⇒
  (fsupdate fs 1 0 (pos + LENGTH s) (insert_atI s pos content)) =
  (add_stdout fs (implode s))
Proof
  rpt strip_tac
  \\ drule STD_streams_stdout \\ rpt strip_tac
  \\ simp [add_stdo_def]
  \\ SELECT_ELIM_TAC
  \\ first_assum $ irule_at (Pos hd)
  \\ rpt strip_tac \\ rveq
  \\ gvs [stdo_def, up_stdo_def, get_file_content_def]
  \\ ‘strlen out = LENGTH (explode out)’ by fs[]
  \\ pop_assum SUBST_ALL_TAC
  \\ rewrite_tac [insert_atI_end]
QED

Theorem fsupdate_add_stdout_str:
  STD_streams fs ∧ get_file_content fs 1 = SOME (content,pos) ⇒
  (fsupdate fs 1 0 (pos + 1) (insert_atI [c] pos content)) =
  (add_stdout fs (str c))
Proof
  rpt strip_tac
  \\ drule_all fsupdate_add_stdout_implode
  \\ disch_then $ qspec_then ‘[c]’ assume_tac
  \\ gvs [str_def]
QED

Theorem fsupdate_add_stderr_implode:
  STD_streams fs ∧ get_file_content fs 2 = SOME (content,pos) ⇒
  (fsupdate fs 2 0 (pos + LENGTH s) (insert_atI s pos content)) =
  (add_stderr fs (implode s))
Proof
  rpt strip_tac
  \\ drule STD_streams_stderr \\ rpt strip_tac
  \\ simp [add_stdo_def]
  \\ SELECT_ELIM_TAC
  \\ first_assum $ irule_at (Pos hd)
  \\ rpt strip_tac \\ rveq
  \\ gvs [stdo_def, up_stdo_def, get_file_content_def]
  \\ ‘strlen out = LENGTH (explode out)’ by fs[]
  \\ pop_assum SUBST_ALL_TAC
  \\ rewrite_tac [insert_atI_end]
QED

Theorem fsupdate_add_stderr:
  STD_streams fs ∧ get_file_content fs 2 = SOME (content,pos) ⇒
  (fsupdate fs 2 0 (pos + strlen s) (insert_atI (explode s) pos content)) =
  (add_stderr fs s)
Proof
  ‘s = implode (explode s)’ by simp []
  \\ pop_assum SUBST_ALL_TAC
  \\ rewrite_tac [strlen_implode, explode_implode]
  \\ rewrite_tac [fsupdate_add_stderr_implode]
QED

Theorem validFD_up_stdo[simp]:
   validFD fd (up_stdo fd' fs out) ⇔ validFD fd fs
Proof
  rw[up_stdo_def]
QED

Theorem validFD_add_stdo[simp]:
   validFD fd (add_stdo fd' nm fs out) ⇔ validFD fd fs
Proof
  rw[add_stdo_def]
QED

Theorem validFileFD_up_stdo[simp]:
   validFileFD fd (up_stdo fd' fs out).infds ⇔ validFileFD fd fs.infds
Proof
  rw[up_stdo_def]
QED

Theorem validFileFD_add_stdo[simp]:
   validFileFD fd (add_stdo fd' nm fs out).infds ⇔ validFileFD fd fs.infds
Proof
  rw[add_stdo_def]
QED

Theorem consistentFS_add_stdout[simp]:
  consistentFS (add_stdout fs s) = consistentFS fs
Proof
  simp [consistentFS_def, add_stdo_def]
QED

Theorem up_stdo_ADELKEY:
   fd ≠ fd' ⇒
   up_stdo fd (fs with infds updated_by ADELKEY fd') out =
   up_stdo fd fs out with infds updated_by ADELKEY fd'
Proof
  rw[up_stdo_def,fsupdate_ADELKEY]
QED

Theorem stdo_ADELKEY:
   fd ≠ fd' ⇒
   stdo fd nm (fs with infds updated_by ADELKEY fd') = stdo fd nm fs
Proof
  rw[stdo_def,FUN_EQ_THM,ALOOKUP_ADELKEY]
QED

Theorem add_stdo_ADELKEY:
   fd ≠ fd' ⇒
   add_stdo fd nm (fs with infds updated_by ADELKEY fd') out =
   add_stdo fd nm fs out with infds updated_by ADELKEY fd'
Proof
  rw[add_stdo_def,up_stdo_ADELKEY,stdo_ADELKEY]
QED

Theorem get_file_content_add_stdout:
   STD_streams fs ∧ fd ≠ 1 ⇒
   get_file_content (add_stdout fs out) fd = get_file_content fs fd
Proof
  rw[get_file_content_def,add_stdo_def,up_stdo_def,fsupdate_def]
  \\ CASE_TAC \\ CASE_TAC \\ simp[AFUPDKEY_ALOOKUP]
  \\ TOP_CASE_TAC \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ CASE_TAC
  >- metis_tac[STD_streams_def,SOME_11,PAIR,FST,SND]
  \\ CASE_TAC
QED

Theorem get_mode_add_stdo[simp]:
   get_mode (add_stdo fd nm fs x) fd' = get_mode fs fd'
Proof
  rw[get_mode_def,add_stdo_def, up_stdo_def, fsupdate_def]
  \\ TOP_CASE_TAC \\ rw[]
  \\ TOP_CASE_TAC \\ rw[]
  \\ simp[AFUPDKEY_ALOOKUP]
  \\ TOP_CASE_TAC \\ rw[]
QED

Theorem get_mode_bumpFD[simp]:
   get_mode (bumpFD fd fs n) fd' = get_mode fs fd'
Proof
  rw[get_mode_def,bumpFD_def,AFUPDKEY_ALOOKUP]
  \\ TOP_CASE_TAC \\ rw[]
QED

Theorem linesFD_add_stdout:
   STD_streams fs ∧ fd ≠ 1 ⇒
   linesFD (add_stdout fs out) fd = linesFD fs fd
Proof
  rw[linesFD_def,get_file_content_add_stdout]
QED

Theorem get_file_content_add_stderr:
   STD_streams fs ∧ fd ≠ 2 ⇒
   get_file_content (add_stderr fs err) fd = get_file_content fs fd
Proof
  rw[get_file_content_def,add_stdo_def,up_stdo_def,fsupdate_def]
  \\ CASE_TAC \\ CASE_TAC \\ simp[AFUPDKEY_ALOOKUP]
  \\ TOP_CASE_TAC \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ CASE_TAC
  >- metis_tac[STD_streams_def,SOME_11,PAIR,FST,SND]
  \\ CASE_TAC
QED

Theorem linesFD_add_stderr:
   STD_streams fs ∧ fd ≠ 2 ⇒
   linesFD (add_stderr fs err) fd = linesFD fs fd
Proof
  rw[linesFD_def,get_file_content_add_stderr]
QED

Theorem up_stdo_forwardFD:
   fd ≠ fd' ⇒ up_stdo fd' (forwardFD fs fd n) out = forwardFD (up_stdo fd' fs out) fd n
Proof
  rw[forwardFD_def,up_stdo_def,fsupdate_def,AFUPDKEY_ALOOKUP]
  \\ CASE_TAC \\ CASE_TAC \\ rw[]
  \\ rpt(AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ match_mp_tac AFUPDKEY_comm \\ rw[]
QED

Theorem up_stdout_fastForwardFD:
   STD_streams fs ⇒
   up_stdout (fastForwardFD fs fd) out = fastForwardFD (up_stdout fs out) fd
Proof
  rw[fastForwardFD_def,up_stdo_def]
  \\ Cases_on`ALOOKUP fs.infds fd` >- (
    fs[miscTheory.the_def,fsupdate_def]
    \\ CASE_TAC \\ fs[miscTheory.the_def]
    \\ CASE_TAC \\ fs[miscTheory.the_def,AFUPDKEY_ALOOKUP] )
  \\ fs[] \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.inode_tbl ino` >- (
    fs[miscTheory.the_def,fsupdate_def]
    \\ CASE_TAC \\ fs[miscTheory.the_def]
    \\ CASE_TAC \\ fs[miscTheory.the_def,AFUPDKEY_ALOOKUP]
    \\ rw[miscTheory.the_def] )
  \\ fs[miscTheory.the_def]
  \\ fs[fsupdate_def,miscTheory.the_def,AFUPDKEY_ALOOKUP]
  \\ CASE_TAC \\ fs[miscTheory.the_def,AFUPDKEY_ALOOKUP]
  >- ( rw[AFUPDKEY_o,o_DEF,PAIR_MAP] )
  \\ CASE_TAC \\ fs[miscTheory.the_def]
  \\ CASE_TAC \\ fs[miscTheory.the_def,AFUPDKEY_ALOOKUP]
  \\ rw[miscTheory.the_def,AFUPDKEY_comm]
  \\ metis_tac[STD_streams_def,SOME_11,PAIR,FST,SND]
QED

Theorem up_stderr_fastForwardFD:
   STD_streams fs ⇒
   up_stderr (fastForwardFD fs fd) out = fastForwardFD (up_stderr fs out) fd
Proof
  rw[fastForwardFD_def,up_stdo_def]
  \\ Cases_on`ALOOKUP fs.infds fd` >- (
    fs[miscTheory.the_def,fsupdate_def]
    \\ CASE_TAC \\ fs[miscTheory.the_def]
    \\ CASE_TAC \\ fs[miscTheory.the_def,AFUPDKEY_ALOOKUP] )
  \\ fs[] \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.inode_tbl ino` >- (
    fs[miscTheory.the_def,fsupdate_def]
    \\ CASE_TAC \\ fs[miscTheory.the_def]
    \\ CASE_TAC \\ fs[miscTheory.the_def,AFUPDKEY_ALOOKUP]
    \\ rw[miscTheory.the_def] )
  \\ fs[miscTheory.the_def]
  \\ fs[fsupdate_def,miscTheory.the_def,AFUPDKEY_ALOOKUP]
  \\ CASE_TAC \\ fs[miscTheory.the_def,AFUPDKEY_ALOOKUP]
  >- ( rw[AFUPDKEY_o,o_DEF,PAIR_MAP] )
  \\ CASE_TAC \\ fs[miscTheory.the_def]
  \\ CASE_TAC \\ fs[miscTheory.the_def,AFUPDKEY_ALOOKUP]
  \\ rw[miscTheory.the_def,AFUPDKEY_comm]
  \\ metis_tac[STD_streams_def,SOME_11,PAIR,FST,SND]
QED

Theorem stdo_forwardFD:
   fd ≠ fd' ⇒ (stdo fd' nm (forwardFD fs fd n) out ⇔ stdo fd' nm fs out)
Proof
  rw[stdo_def,forwardFD_def,AFUPDKEY_ALOOKUP]
  \\ CASE_TAC
QED

Theorem stdo_fastForwardFD:
   fd ≠ fd' ⇒ (stdo fd' nm (fastForwardFD fs fd) out ⇔ stdo fd' nm fs out)
Proof
  rw[stdo_def,fastForwardFD_def,AFUPDKEY_ALOOKUP]
  \\ Cases_on`ALOOKUP fs.infds fd` \\ fs[miscTheory.the_def]
  \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.inode_tbl ino` \\ fs[miscTheory.the_def]
  \\ fs[AFUPDKEY_ALOOKUP] \\ rw[]
  \\ CASE_TAC
QED

Theorem add_stdo_forwardFD:
   fd ≠ fd' ⇒ add_stdo fd' nm (forwardFD fs fd n) out = forwardFD (add_stdo fd' nm fs out) fd n
Proof
  rw[add_stdo_def,stdo_forwardFD,up_stdo_forwardFD]
QED

Theorem add_stdout_lineForwardFD:
   STD_streams fs ∧ fd ≠ 1 ⇒
   add_stdout (lineForwardFD fs fd) out = lineForwardFD (add_stdout fs out) fd
Proof
  rw[lineForwardFD_def,get_file_content_add_stdout]
  \\ CASE_TAC \\ CASE_TAC
  \\ rw[] \\ pairarg_tac \\ fs[add_stdo_forwardFD]
QED

Theorem add_stdout_fastForwardFD:
   STD_streams fs ∧ fd ≠ 1 ⇒
   add_stdout (fastForwardFD fs fd) out = fastForwardFD (add_stdout fs out) fd
Proof
  rw[add_stdo_def,up_stdout_fastForwardFD,stdo_fastForwardFD]
QED

Theorem add_stderr_lineForwardFD:
   STD_streams fs ∧ fd ≠ 2 ⇒
   add_stderr (lineForwardFD fs fd) out = lineForwardFD (add_stderr fs out) fd
Proof
  rw[lineForwardFD_def,get_file_content_add_stderr]
  \\ CASE_TAC \\ CASE_TAC
  \\ rw[] \\ pairarg_tac \\ fs[add_stdo_forwardFD]
QED

Theorem add_stderr_fastForwardFD:
   STD_streams fs ∧ fd ≠ 2 ⇒
   add_stderr (fastForwardFD fs fd) out = fastForwardFD (add_stderr fs out) fd
Proof
  rw[add_stdo_def,up_stderr_fastForwardFD,stdo_fastForwardFD]
QED

Theorem FILTER_File_add_stdo:
   stdo fd nm fs init ⇒
   FILTER (isFile o FST) (add_stdo fd nm fs out).inode_tbl = FILTER (isFile o FST) fs.inode_tbl
Proof
  rw[add_stdo_def,up_stdo_def,fsupdate_def]
  \\ CASE_TAC \\ CASE_TAC \\ fs[]
  \\ match_mp_tac FILTER_EL_EQ \\ simp[]
  \\ qmatch_assum_rename_tac`_ = SOME (k,_)`
  \\ qx_gen_tac`n`
  \\ simp[GSYM AND_IMP_INTRO] \\ strip_tac
  \\ reverse(Cases_on`FST (EL n fs.inode_tbl) = k`)
  >- simp[EL_AFUPDKEY_unchanged]
  \\ simp[FST_EL_AFUPDKEY,GSYM AND_IMP_INTRO]
  \\ fs[stdo_def]
QED

Theorem FILTER_File_add_stdout:
   STD_streams fs ⇒
   FILTER (isFile o FST) (add_stdout fs out).inode_tbl = FILTER (isFile o FST) fs.inode_tbl
Proof
  metis_tac[STD_streams_stdout,FILTER_File_add_stdo]
QED

Theorem FILTER_File_add_stderr:
   STD_streams fs ⇒
   FILTER (isFile o FST) (add_stderr fs out).inode_tbl = FILTER (isFile o FST) fs.inode_tbl
Proof
  metis_tac[STD_streams_stderr,FILTER_File_add_stdo]
QED

(* Note: more general versions of the following 4 theorems
  can be proved for stdo, but requires
  assumption to ensure that the file descriptors do not overlap *)
Theorem stdout_add_stderr:
  STD_streams fs ∧ stdout fs out ⇒
  stdout (add_stderr fs err) out
Proof
  rw[stdo_def,implode_def]>>
  simp[add_stdo_def,up_stdo_def,fsupdate_def]>>
  every_case_tac>>simp[AFUPDKEY_ALOOKUP]>>
  fs[STD_streams_def]>>
  rw[]>>simp[]>>
  Cases_on`r`>>
  rpt(first_x_assum(qspecl_then [`2`,`q`,`r'`] assume_tac))>>fs[]
QED

Theorem stderr_add_stdout:
  STD_streams fs ∧ stderr fs err ⇒
  stderr (add_stdout fs out) err
Proof
  rw[stdo_def,implode_def]>>
  simp[add_stdo_def,up_stdo_def,fsupdate_def]>>
  every_case_tac>>simp[AFUPDKEY_ALOOKUP]>>
  fs[STD_streams_def]>>
  rw[]>>simp[]>>
  Cases_on`r`>>
  rpt(first_x_assum(qspecl_then [`1`,`q`,`r'`] assume_tac))>>fs[]
QED

Theorem add_stdout_inj:
  add_stdout fs1 out1 = add_stdout fs2 out2 ∧
  stdout fs1 out ∧ stdout fs2 out ⇒
  out1 = out2
Proof
  rw[]>>
  `stdout (add_stdout fs1 out1) (out ^ out1)` by
    metis_tac[stdo_add_stdo]>>
  `stdout (add_stdout fs2 out2) (out ^ out2)` by
    metis_tac[stdo_add_stdo]>>
  fs[fsFFITheory.IO_fs_component_equality]>>
  rw[]>>fs[stdo_def]>>
  gs[]
QED

Theorem add_stderr_inj:
  add_stderr fs1 err1 = add_stderr fs2 err2 ∧
  stderr fs1 err ∧ stderr fs2 err ⇒
  err1 = err2
Proof
  rw[]>>
  `stderr (add_stderr fs1 err1) (err ^ err1)` by
    metis_tac[stdo_add_stdo]>>
  `stderr (add_stderr fs2 err2) (err ^ err2)` by
    metis_tac[stdo_add_stdo]>>
  fs[fsFFITheory.IO_fs_component_equality]>>
  rw[]>>fs[stdo_def]>>
  gs[]
QED

Definition stdin_def:
  stdin fs inp pos = (ALOOKUP fs.infds 0 = SOME(UStream(strlit"stdin"),ReadMode,pos) /\
                     ALOOKUP fs.inode_tbl (UStream(strlit"stdin"))= SOME inp)
End

Definition up_stdin_def:
  up_stdin inp pos fs = fsupdate fs 0 0 pos inp
End

Definition get_stdin_def:
  get_stdin fs = let (inp,pos) = @(inp,pos). stdin fs inp pos in DROP pos inp
End

Theorem stdin_11:
   stdin fs i1 p1 ∧ stdin fs i2 p2 ⇒ i1 = i2 ∧ p1 = p2
Proof
  rw[stdin_def] \\ fs[]
QED

Theorem stdin_get_file_content:
   stdin fs inp pos ⇒ get_file_content fs 0 = SOME (inp,pos)
Proof
  rw[stdin_def,fsFFITheory.get_file_content_def]
QED

Theorem stdin_forwardFD:
   stdin fs inp pos ⇒
   stdin (forwardFD fs fd n) inp (if fd = 0 then pos+n else pos)
Proof
  rw[stdin_def,forwardFD_def]
  \\ simp[AFUPDKEY_ALOOKUP]
QED

Theorem stdin_get_stdin:
   stdin fs inp pos ⇒ get_stdin fs = DROP pos inp
Proof
  rw[get_stdin_def]
  \\ SELECT_ELIM_TAC
  \\ rw[EXISTS_PROD,FORALL_PROD]
  >- metis_tac[]
  \\ pairarg_tac \\ fs[]
  \\ imp_res_tac stdin_11 \\ fs[]
QED

Theorem get_stdin_forwardFD:
   stdin fs inp pos ⇒
   get_stdin (forwardFD fs fd n) =
   if fd = 0 then
     DROP n (get_stdin fs)
   else get_stdin fs
Proof
  strip_tac
  \\ imp_res_tac stdin_get_stdin
  \\ imp_res_tac stdin_forwardFD
  \\ first_x_assum(qspecl_then[`n`,`fd`]mp_tac)
  \\ strip_tac
  \\ simp[DROP_DROP_T]
  \\ imp_res_tac stdin_get_stdin
  \\ rw[]
QED

Theorem linesFD_splitlines_get_stdin:
   stdin fs inp pos ⇒
    MAP (λl. l ++ "\n") (splitlines (get_stdin fs)) = linesFD fs 0
Proof
  rw[linesFD_def]
  \\ imp_res_tac stdin_get_stdin
  \\ fs[stdin_def,get_file_content_def]
QED

(* file descriptors are encoded on 8 bytes *)
Definition FD_def:
  FD fd fdv = (STRING_TYPE (implode(MAP (CHR ∘ w2n) (n2w8 fd))) fdv ∧ fd < 256**8)
End

Definition INSTREAM_def:
  INSTREAM fd fdv <=>
    INSTREAM_TYPE (Instream (implode(MAP (CHR ∘ w2n) (n2w8 fd)))) fdv ∧
    fd < 256**8
End

Definition OUTSTREAM_def:
  OUTSTREAM fd fdv <=>
    OUTSTREAM_TYPE (Outstream (implode(MAP (CHR ∘ w2n) (n2w8 fd)))) fdv ∧
    fd < 256**8
End

Theorem INSTREAM_stdin:
   INSTREAM 0 raw_stdin_v
Proof
  fs[INSTREAM_def,MarshallingTheory.n2w8_def,raw_stdin_v_thm,GSYM raw_stdIn_def]
QED

Theorem OUTSTREAM_stdout:
   OUTSTREAM 1 stdout_v
Proof
  fs[OUTSTREAM_def,MarshallingTheory.n2w8_def,stdout_v_thm,GSYM stdOut_def]
QED

Theorem OUTSTREAM_stderr:
   OUTSTREAM 2 stderr_v
Proof
  fs[OUTSTREAM_def,MarshallingTheory.n2w8_def,stderr_v_thm,GSYM stdErr_def]
QED

Definition REF_NUM_def:
  REF_NUM loc n =
    SEP_EXISTS v. REF loc v * & (NUM n v)
End

Definition instream_buffered_inv_def:
  instream_buffered_inv r w bcontent bactive =
      (1028 <= LENGTH bcontent  /\
       LENGTH bcontent < 256**2 /\
      4 <= w /\
      4 <= r /\
      r <= LENGTH bcontent /\
      w <= LENGTH bcontent /\
      r <= w /\
      LENGTH bactive = w - r /\
      LENGTH bactive < LENGTH bcontent /\
      bactive = TAKE (w-r) (DROP r bcontent))
End
      (*(bactive = [] <=> r = w))*)

Theorem instream_buffered_inv_alt:
  instream_buffered_inv r w bcontent bactive =
    ∃old unused.
      bcontent = old ++ bactive ++ unused ∧
      1028 <= LENGTH bcontent /\
      LENGTH bcontent < 256**2 /\
      4 <= LENGTH old /\
      LENGTH (old ++ bactive) = w /\
      LENGTH old = r
Proof
  reverse eq_tac \\ gvs [instream_buffered_inv_def]
  >-
   (rw [] \\ gvs []
    \\ once_rewrite_tac [GSYM APPEND_ASSOC]
    \\ rewrite_tac [DROP_LENGTH_APPEND,TAKE_LENGTH_APPEND])
  \\ strip_tac
  \\ qpat_x_assum ‘r ≤ LENGTH bcontent’ assume_tac
  \\ drule LESS_EQ_LENGTH \\ strip_tac \\ gvs []
  \\ qexists_tac ‘ys1’ \\ gvs [DROP_LENGTH_APPEND]
  \\ pop_assum mp_tac
  \\ rewrite_tac [LESS_EQ_EXISTS] \\ strip_tac \\ gvs []
  \\ ‘p ≤ LENGTH ys2’ by gvs []
  \\ drule LESS_EQ_LENGTH \\ strip_tac \\ gvs [TAKE_LENGTH_APPEND]
QED

Overload TypeStamp_InstreamBuffered = “TypeStamp «InstreamBuffered» 35”;

Definition INSTREAM_BUFFERED_def:
  INSTREAM_BUFFERED bactive is =
    SEP_EXISTS rr r wr w buff bcontent fd fdv.
      & (is = (Conv instreambuffered_con_stamp [fdv; rr; wr; buff]) /\
        INSTREAM fd fdv /\
        instream_buffered_inv r w bcontent bactive) *
      REF_NUM rr r *
      REF_NUM wr w *
      W8ARRAY buff bcontent
End

Definition INSTREAM_BUFFERED_FD_def:
  INSTREAM_BUFFERED_FD bactive fd is =
    SEP_EXISTS rr r wr w buff bcontent fdv.
      & (is = (Conv instreambuffered_con_stamp [fdv; rr; wr; buff]) /\
        INSTREAM fd fdv /\
        instream_buffered_inv r w bcontent bactive) *
      REF_NUM rr r *
      REF_NUM wr w *
      W8ARRAY buff bcontent
End

Definition INSTREAM_BUFFERED_BL_FD_def:
  INSTREAM_BUFFERED_BL_FD bcontent bactive fd is =
    SEP_EXISTS rr r wr w buff fdv.
      & (is = (Conv instreambuffered_con_stamp [fdv; rr; wr; buff]) /\
        INSTREAM fd fdv /\
        instream_buffered_inv r w bcontent bactive) *
      REF_NUM rr r *
      REF_NUM wr w *
      W8ARRAY buff bcontent
End

Definition INSTREAM_BUFFERED_BL_FD_RW_def:
  INSTREAM_BUFFERED_BL_FD_RW bcontent bactive fd r w is =
    SEP_EXISTS rr wr buff fdv.
      & (is = (Conv instreambuffered_con_stamp [fdv; rr; wr; buff]) /\
        INSTREAM fd fdv /\
        instream_buffered_inv r w bcontent bactive) *
      REF_NUM rr r *
      REF_NUM wr w *
      W8ARRAY buff bcontent
End
(* -- *)

Theorem raw_openIn_spec:
   ∀s sv fs.
     FILENAME s sv ∧
     hasFreeFD fs ⇒
     app (p:'ffi ffi_proj) TextIO_raw_openIn_v [sv]
       (IOFS fs)
       (POSTve
          (\fdv. &(INSTREAM (nextFD fs) fdv ∧
                  validFD (nextFD fs) (openFileFS s fs ReadMode 0) ∧
                  inFS_fname fs s) *
                IOFS (openFileFS s fs ReadMode 0))
          (\e. &(BadFileName_exn e ∧ ~inFS_fname fs s) * IOFS fs))
Proof
  rw [] >> qpat_abbrev_tac `Q = POSTve _ _` >>
  simp [IOFS_def, fs_ffi_part_def, IOx_def, IO_def] >>
  xpull >> qunabbrev_tac `Q` >>
  rpt strip_tac >>
  xcf_with_def TextIO_raw_openIn_v_def >>
  fs[FILENAME_def, strlen_def, IOFS_def, IOFS_iobuff_def] >>
  REVERSE (Cases_on`consistentFS fs`) >-(xpull >> fs[wfFS_def]) >>
  xpull >> rename [`W8ARRAY _ fnm0`] >>
  qmatch_goalsub_abbrev_tac`catfs fs * _` >>
  rpt (xlet_auto >- xsimpl) >>
  qmatch_goalsub_abbrev_tac`W8ARRAY _ fd0` >>
  qmatch_goalsub_rename_tac`W8ARRAY loc fd0` >>
  qmatch_goalsub_abbrev_tac`catfs fs' * _` >>
  Cases_on `inFS_fname fs s`
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
        imp_res_tac inFS_fname_ALOOKUP_EXISTS >>
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
    xcon >>
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
  simp[BadFileName_exn_def,Abbr`fd0`,LENGTH_explode]
QED

(* STDIO version *)
Theorem raw_openIn_STDIO_spec:
   ∀s sv fs.
     FILENAME s sv ∧
     hasFreeFD fs ⇒
     app (p:'ffi ffi_proj) TextIO_raw_openIn_v [sv]
       (STDIO fs)
       (POSTve
          (\fdv. &(INSTREAM (nextFD fs) fdv ∧
                  validFD (nextFD fs) (openFileFS s fs ReadMode 0) ∧
                  inFS_fname fs s) *
                STDIO (openFileFS s fs ReadMode 0))
          (\e. &(BadFileName_exn e ∧ ~inFS_fname fs s) * STDIO fs))
Proof
 rw[STDIO_def] >> xpull >> xapp_spec raw_openIn_spec >>
 map_every qexists_tac [`emp`,`s`,`fs with numchars := ll`] >>
 xsimpl >> rw[] >> qexists_tac`ll` >> fs[openFileFS_fupd_numchars] >> xsimpl >>
 rw[] >>
 fs[nextFD_numchars,nextFD_numchars,openFileFS_fupd_numchars,STD_streams_openFileFS] >>
 fs[GSYM validFD_numchars,GSYM openFileFS_fupd_numchars,inFS_fname_numchars]
QED

(* openOut, openAppend here *)

Theorem raw_closeIn_spec:
   ∀fdw fdv fs.
     INSTREAM fdw fdv ⇒
     app (p:'ffi ffi_proj) TextIO_raw_closeIn_v [fdv]
       (IOFS fs)
       (POSTve
          (\u. &(UNIT_TYPE () u /\ validFileFD fdw fs.infds) *
               IOFS (fs with infds updated_by ADELKEY fdw))
          (\e. &(InvalidFD_exn e /\ ¬ validFileFD fdw fs.infds) * IOFS fs))
Proof
  rw [] >> qpat_abbrev_tac `Q = POSTve _ _` >>
  simp [IOFS_def, fs_ffi_part_def, IOx_def, IO_def] >>
  xpull >> qunabbrev_tac `Q` >>
  rpt strip_tac >>
  xcf_with_def TextIO_raw_closeIn_v_def >>
  fs[IOFS_def, IOFS_iobuff_def,INSTREAM_def] >> xpull >>
  rename [`W8ARRAY _ buf`] >> cases_on`buf` >> fs[LUPDATE_def] >>
  xlet_auto >- xsimpl >> fs [get_in_def] >>
  xlet`POSTv uv. &(UNIT_TYPE () uv) *
        W8ARRAY iobuff_loc ((if validFileFD fdw fs.infds then 0w else 1w) ::t) *
        IOx fs_ffi_part (if validFileFD fdw fs.infds then
                            (fs with infds updated_by ADELKEY fdw)
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
     cases_on`fs` >> fs[recordtype_IO_fs_seldef_infds_fupd_def] >>
     imp_res_tac ALOOKUP_NONE >> rw[] \\
     fs[liveFS_def,recordtype_IO_fs_seldef_infds_fupd_def,STRING_TYPE_def] \\ xsimpl >>
     qpat_abbrev_tac `new_events = events ++ _` >>
     qexists_tac `new_events` >> xsimpl) >>
  NTAC 3 (xlet_auto >- xsimpl) >>
  xif >-(xcon >> fs [CaseEq"bool"] >> xsimpl) >>
  xlet_auto >-(xcon >> xsimpl) >>
  xraise >> fs[InvalidFD_exn_def,IOFS_def,CaseEq"bool"] >> xsimpl
QED

Theorem closeOut_spec:
   ∀fdw fdv fs.
     OUTSTREAM fdw fdv ⇒
     app (p:'ffi ffi_proj) TextIO_closeOut_v [fdv]
       (IOFS fs)
       (POSTve
         (\u. &(UNIT_TYPE () u /\ validFileFD fdw fs.infds) *
              IOFS (fs with infds updated_by ADELKEY fdw))
         (\e. &(InvalidFD_exn e /\ ¬ validFileFD fdw fs.infds) * IOFS fs))
Proof
  rw [] >> qpat_abbrev_tac `Q = POSTve _ _` >>
  simp [IOFS_def, fs_ffi_part_def, IOx_def, IO_def] >>
  xpull >> qunabbrev_tac `Q` >>
  rpt strip_tac >>
  xcf_with_def TextIO_closeOut_v_def >>
  fs[IOFS_def, IOFS_iobuff_def,OUTSTREAM_def] >> xpull >>
  rename [`W8ARRAY _ buf`] >> cases_on`buf` >> fs[LUPDATE_def] >>
  xlet_auto >- xsimpl >> fs [get_out_def] >>
  xlet`POSTv uv. &(UNIT_TYPE () uv) *
        W8ARRAY iobuff_loc ((if validFileFD fdw fs.infds then 0w else 1w) ::t) *
        IOx fs_ffi_part (if validFileFD fdw fs.infds then
                            (fs with infds updated_by ADELKEY fdw)
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
     cases_on`fs` >> fs[recordtype_IO_fs_seldef_infds_fupd_def] >>
     imp_res_tac ALOOKUP_NONE >> rw[] \\
     fs[liveFS_def,recordtype_IO_fs_seldef_infds_fupd_def,STRING_TYPE_def] \\ xsimpl >>
     qpat_abbrev_tac `new_events = events ++ _` >>
     qexists_tac `new_events` >> xsimpl) >>
  NTAC 3 (xlet_auto >- xsimpl) >>
  xif >-(xcon >> fs [CaseEq"bool"] >> xsimpl) >>
  xlet_auto >-(xcon >> xsimpl) >>
  xraise >> fs[InvalidFD_exn_def,IOFS_def,CaseEq"bool"] >> xsimpl
QED

Theorem raw_closeIn_STDIO_spec:
   ∀fd fs fdv.
     INSTREAM fd fdv /\ fd >= 3 /\ fd <= fs.maxFD ⇒
     app (p:'ffi ffi_proj) TextIO_raw_closeIn_v [fdv]
       (STDIO fs)
       (POSTve
          (\u. &(UNIT_TYPE () u /\ validFileFD fd fs.infds) *
               STDIO (fs with infds updated_by ADELKEY fd))
          (\e. &(InvalidFD_exn e /\ ¬ validFileFD fd fs.infds) * STDIO fs))
Proof
  rw[STDIO_def] >> xpull >> xapp_spec raw_closeIn_spec >>
  map_every qexists_tac [`emp`,`fs with numchars := ll`,`fd`] >>
  xsimpl >> rw[] >> qexists_tac`ll` >> fs[validFileFD_def] >> xsimpl >>
  fs[STD_streams_def,ALOOKUP_ADELKEY] \\
  Cases_on`fd = 0` \\ fs[]
  \\ Cases_on`fd = 1` \\ fs[]
  \\ Cases_on`fd = 2` \\ fs[]
  \\ metis_tac[]
QED

Theorem closeOut_STDIO_spec:
   ∀fd fs fdv.
     OUTSTREAM fd fdv /\ fd >= 3 /\ fd <= fs.maxFD ⇒
     app (p:'ffi ffi_proj) TextIO_closeOut_v [fdv]
       (STDIO fs)
       (POSTve
          (\u. &(UNIT_TYPE () u /\ validFileFD fd fs.infds) *
               STDIO (fs with infds updated_by ADELKEY fd))
          (\e. &(InvalidFD_exn e /\ ¬ validFileFD fd fs.infds) * STDIO fs))
Proof
  rw[STDIO_def] >> xpull >> xapp_spec closeOut_spec >>
  map_every qexists_tac [`emp`,`fs with numchars := ll`,`fd`] >>
  xsimpl >> rw[] >> qexists_tac`ll` >> fs[validFileFD_def] >> xsimpl >>
  fs[STD_streams_def,ALOOKUP_ADELKEY] \\
  Cases_on`fd = 0` \\ fs[]
  \\ Cases_on`fd = 1` \\ fs[]
  \\ Cases_on`fd = 2` \\ fs[]
  \\ metis_tac[]
QED

Theorem writei_spec:
  wfFS fs ⇒ 0 < n ⇒
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
         IOFS (fs with numchars:= THE(LDROP (1 + Lnext_pos fs.numchars) fs.numchars))))
Proof
  strip_tac >>
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
  rpt strip_tac >>
  xcf_with_def TextIO_writei_v_def >> fs[FD_def]
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
     xif >> fs[FALSE_def] >> xvar >> xsimpl >>
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
     fs [fs_ffi_part_def, IOx_def, IO_def] >>
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
     pairarg_tac >> fs[AFUPDKEY_unchanged,LDROP_1]) >>
  fs[Abbr`fs'`,get_file_content_def,liveFS_def,live_numchars_def,fsupdate_def,LDROP_1,
     wfFS_fsupdate,validFD_def,liveFS_fsupdate,IOFS_def] >>
  pairarg_tac >> fs[AFUPDKEY_unchanged] >>
  fs[wfFS_def,liveFS_def,live_numchars_def] >>
  imp_res_tac always_thm >>
  `Lnext_pos (0:::t) = SUC(Lnext_pos t)` by
    (fs[Lnext_pos_def,Once Lnext_def]) >>
  csimp[ADD] >> xsimpl >> cases_on`t` >>
  fs[get_mode_def] >> rw[] >> instantiate >> xsimpl
QED

Theorem write_spec:
   !n fs fd i pos h1 h2 h3 h4 rest bc fdv nv iv content.
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
                                     content)))
Proof
  strip_tac >> `?N. n <= N` by (qexists_tac`n` >> fs[]) >>
  FIRST_X_ASSUM MP_TAC >> qid_spec_tac`n` >>
  Induct_on`N` >>
  rpt strip_tac >>
  xcf_with_def TextIO_write_v_def
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
     fs[wfFS_fsupdate,validFD_def,always_DROP,AFUPDKEY_ALOOKUP,
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
                         always_DROP,AFUPDKEY_ALOOKUP,get_file_content_def,get_mode_def] >>
                  pairarg_tac >> fs[fsupdate_def,always_DROP,AFUPDKEY_ALOOKUP] >>
          imp_res_tac NOT_LFINITE_DROP >>
          FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC`(Lnext_pos fs.numchars + 1)`) >>
          fs[] >> imp_res_tac NOT_LFINITE_DROP_LFINITE)) >>
  rw[] >> qexists_tac`Lnext_pos fs.numchars + 1 + x` >>
  fs[wfFS_def,fsupdate_o,Abbr`fs'`,insert_atI_insert_atI] >>
  qmatch_abbrev_tac`_ (_ _ _ _ _ (_ c1 _ _)) ==>> _ (_ _ _ _ _ (_ c2 _ _)) * _` >>
  `c1 = c2` suffices_by xsimpl >> fs[Abbr`c1`,Abbr`c2`] >>
  PURE_REWRITE_TAC[Once (Q.SPECL [`i`,`nw`] ADD_COMM)] >>
  fs[Once ADD_COMM,GSYM DROP_DROP_T,take_drop_partition,MAP_DROP]
QED

Theorem output1_spec:
   !fd fdv c cv bc content pos.
    get_file_content fs fd = SOME(content, pos) ⇒
    get_mode fs fd = SOME WriteMode ⇒
    CHAR c cv ⇒ OUTSTREAM fd fdv ⇒
    app (p:'ffi ffi_proj) TextIO_output1_v [fdv; cv]
    (IOFS fs)
    (POSTv uv.
      &UNIT_TYPE () uv * SEP_EXISTS k.
      IOFS (fsupdate fs fd k (pos+1) (insert_atI [c] pos content)))
Proof
  rpt strip_tac >>
  xcf_with_def TextIO_output1_v_def >>
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
  fs[CHR_ORD,LESS_MOD,ORD_BOUND] >> qexists_tac`k` >> xsimpl
QED

Theorem output1_STDIO_spec:
   !fd. get_file_content fs fd = SOME(content, pos) ∧
        get_mode fs fd = SOME WriteMode ∧
   CHAR c cv ∧ OUTSTREAM fd fdv ⇒
   app (p:'ffi ffi_proj) TextIO_output1_v [fdv; cv]
   (STDIO fs)
   (POSTv uv.
     &UNIT_TYPE () uv *
     STDIO (fsupdate fs fd 0 (pos+1) (insert_atI [c] pos content)))
Proof
  rw[STDIO_def] \\ xpull \\ xapp_spec output1_spec \\
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
  \\ rw[Abbr`fs1`,Abbr`fs2`,IO_fs_component_equality,fsupdate_def]
QED

Theorem output1_stdOut_spec:
  CHAR c cv ⇒
  app (p:'ffi ffi_proj) TextIO_output1_v [stdout_v; cv]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv * STDIO (add_stdout fs (str c)))
Proof
  strip_tac
  \\ rewrite_tac [Once STDIO_STD_streams] \\ xpull
  \\ drule get_file_content_stdout \\ rpt strip_tac
  \\ xapp_spec output1_STDIO_spec
  \\ instantiate
  \\ simp [OUTSTREAM_stdout, Req0 STD_streams_get_mode] \\ xsimpl
  \\ simp [Req0 fsupdate_add_stdout_str] \\ xsimpl
QED

val tac =
     simp[w82n_n2w8,FD_def,LENGTH_n2w8,STRING_TYPE_def] \\ xsimpl
  \\ imp_res_tac STD_streams_stdout
  \\ imp_res_tac STD_streams_stderr
  \\ simp[add_stdo_def,up_stdo_def]
  \\ SELECT_ELIM_TAC \\ conj_tac >- metis_tac[]
  \\ rw[] \\ imp_res_tac stdo_UNICITY_R \\ rveq
  \\ fs[stdo_def,get_file_content_def,get_mode_def,implode_def,STRING_TYPE_def,PULL_EXISTS]
  \\ instantiate \\ xsimpl
  \\ conj_tac >- (EVAL_TAC \\ simp[EVAL_RULE stdout_v_thm,EVAL_RULE stderr_v_thm])
  \\ simp[Q.ISPEC`explode x`(Q.GEN`l2`insert_atI_end) |> SIMP_RULE(srw_ss())[]]
  \\ xsimpl;

Theorem output1_stdout_spec:
   CHAR c cv ∧ fdv = stdout_v ==>
   app (p:'ffi ffi_proj) TextIO_output1_v
     [fdv; cv] (STDIO fs)
     (POSTv uv. &UNIT_TYPE () uv * STDIO (add_stdout fs (str c)))
Proof
  reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ strip_tac \\ xpull)
  \\ strip_tac
  \\ xapp_spec output1_STDIO_spec
  \\ tac
QED

Theorem output1_stderr_spec:
   CHAR c cv ∧ fdv = stderr_v ==>
   app (p:'ffi ffi_proj) TextIO_output1_v
     [fdv; cv] (STDIO fs)
     (POSTv uv. &UNIT_TYPE () uv * STDIO (add_stderr fs (str c)))
Proof
  reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ strip_tac \\ xpull)
  \\ strip_tac
  \\ xapp_spec output1_STDIO_spec
  \\ tac
QED

Theorem output_spec:
   !s fd fdv sv fs content pos.
    OUTSTREAM fd fdv ⇒ STRING_TYPE s sv ⇒
    (get_file_content fs fd = SOME(content, pos)) ⇒
    (get_mode fs fd = SOME WriteMode) ⇒
    app (p:'ffi ffi_proj) TextIO_output_v [fdv; sv]
    (IOFS fs)
    (POSTv uv. &(UNIT_TYPE () uv) *
       SEP_EXISTS k. IOFS (fsupdate fs fd k (pos + (strlen s))
                                    (insert_atI (explode s) pos content)))
Proof
  strip_tac >>
  `?n. strlen s <= n` by (qexists_tac`strlen s` >> fs[]) >>
  FIRST_X_ASSUM MP_TAC >> qid_spec_tac`s` >>
  Induct_on`n` >>
  rpt strip_tac >>
  xcf_with_def TextIO_output_v_def >>
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
     AFUPDKEY_ALOOKUP,extract_def,strlen_extract_le,
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
    fs[AFUPDKEY_o] >>
    match_mp_tac AFUPDKEY_eq >>
    fs[PAIR_MAP_THM,FORALL_PROD] ) >>
  fs[AFUPDKEY_o] >>
  match_mp_tac AFUPDKEY_eq >>
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
  \\ Cases_on`s` \\ fs[substring_def,SEG_TAKE_DROP,TAKE_LENGTH_ID_rwt]
QED

Theorem output_STDIO_spec:
   !fd fdv fs content pos s.
   OUTSTREAM fd fdv ∧ get_file_content fs fd = SOME (content,pos) ∧ get_mode fs fd = SOME WriteMode ∧ STRING_TYPE s sv ⇒
   app (p:'ffi ffi_proj) TextIO_output_v [fdv;sv]
   (STDIO fs)
   (POSTv uv. &(UNIT_TYPE () uv) *
      STDIO (fsupdate fs fd 0 (pos+strlen s) (insert_atI (explode s) pos content)))
Proof
  rpt strip_tac
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
  rw[] \\ fs[] \\ simp[insert_atI_end,LENGTH_explode]
QED

Theorem print_spec:
   !fs sv s.
    STRING_TYPE s sv ⇒
    app (p:'ffi ffi_proj) TextIO_print_v [sv]
    (STDIO fs)
    (POSTv uv. &(UNIT_TYPE () uv) * STDIO (add_stdout fs s))
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_print_v_def
  \\ reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull)
  \\ xapp_spec output_STDIO_spec
  \\ tac
QED

Definition print_def:
  print s = (\fs. (M_success (), add_stdout fs s))
End

Theorem EvalM_print:
   Eval env exp (STRING_TYPE x) /\
   (nsLookup env.v (Short «print») = SOME TextIO_print_v) ==>
    EvalM F env st (App Opapp [Var (Short «print»); exp])
      (MONAD UNIT_TYPE exc_ty (print x))
      (MONAD_IO,p:'ffi ffi_proj)
Proof
    ho_match_mp_tac EvalM_from_app \\ rw [print_def]
    \\ fs [MONAD_IO_def]
    \\ xpull
    \\ fs [SEP_CLAUSES]
    \\ xapp_spec print_spec
    \\ fs[]
QED

Theorem output_stderr_spec:
   !fs sv s fdv.
    STRING_TYPE s sv ∧ fdv = stderr_v ⇒
    app (p:'ffi ffi_proj) TextIO_output_v [fdv;sv]
    (STDIO fs)
    (POSTv uv. &(UNIT_TYPE () uv) * STDIO (add_stderr fs s))
Proof
  rpt strip_tac
  \\ rewrite_tac [Once STDIO_STD_streams] \\ xpull
  \\ xapp_spec output_STDIO_spec
  \\ tac
QED

Theorem print_err_spec:
   !fs sv s.
    STRING_TYPE s sv ⇒
    app (p:'ffi ffi_proj) TextIO_print_err_v [sv]
    (STDIO fs)
    (POSTv uv. &(UNIT_TYPE () uv) * STDIO (add_stderr fs s))
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_print_err_v_def
  \\ reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull)
  \\ xapp_spec output_stderr_spec \\ fs []
QED

Definition print_err_def:
  print_err s = (\fs. (M_success (), add_stderr fs s))
End

Theorem EvalM_print_err:
   Eval env exp (STRING_TYPE x) /\
    (nsLookup env.v (Long «TextIO» (Short «print_err»)) =
      SOME TextIO_print_err_v) ==>
    EvalM F env st (App Opapp [Var (Long «TextIO» (Short «print_err»)); exp])
      (MONAD UNIT_TYPE exc_ty (print_err x))
      (MONAD_IO,p:'ffi ffi_proj)
Proof
    ho_match_mp_tac EvalM_from_app \\ rw [print_err_def]
    \\ fs [MONAD_IO_def]
    \\ xpull
    \\ fs [SEP_CLAUSES]
    \\ xapp_spec print_err_spec
    \\ fs[]
QED

Theorem read_spec:
  !fs fd fdv n nv. wfFS fs ⇒ FD fd fdv ⇒ NUM n nv ⇒
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
     (\e. &InvalidFD_exn e * &(get_file_content fs fd = NONE ∨ get_mode fs fd ≠ SOME ReadMode) * IOFS fs))
Proof
   rpt strip_tac >>
   xcf_with_def TextIO_read_v_def >>
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
  simp[GSYM n2w2_def,w22n_n2w2] >> xsimpl >> gvs []
QED

Theorem read_into_spec:
  !fs fd fdv n nv buf. wfFS fs ⇒ FD fd fdv ⇒ NUM n nv ⇒
   n < 256**2 ⇒ MAX n 1024 <= LENGTH rest ⇒
   app (p:'ffi ffi_proj) TextIO_read_into_v [fdv;buf;nv]
   (W8ARRAY buf (h1::h2::h3::h4::rest) * IOx fs_ffi_part fs)
   (POSTve
     (\nrv. SEP_EXISTS (nr : num).
      &(NUM nr nrv) *
      SEP_EXISTS content pos.
        &(get_file_content fs fd = SOME(content, pos) /\
          get_mode fs fd = SOME ReadMode /\
          (nr <= MIN n (LENGTH content - pos) /\
           nr <= LENGTH content - pos) /\
          (nr = 0 ⇔ eof fd fs = SOME T ∨ n = 0)) *
      IOx fs_ffi_part (bumpFD fd fs nr) *
      W8ARRAY buf (0w :: n2w (nr DIV 256) :: n2w nr :: h4::
        MAP (n2w o ORD) (TAKE nr (DROP pos content))++DROP nr rest))
     (\e. &InvalidFD_exn e * &(get_file_content fs fd = NONE ∨ get_mode fs fd ≠ SOME ReadMode) * IOFS_WO_iobuff fs))
Proof
   rpt strip_tac >>
   xcf_with_def TextIO_read_into_v_def >>
   fs[IOFS_WO_iobuff_def] >>
   xlet_auto >- xsimpl >>
   simp[insert_atI_def,n2w2_def] >>
   cases_on`get_file_content fs fd`
   >-(xlet`POSTv v. W8ARRAY buf (1w::n2w n::h3::h4::rest) * IOx fs_ffi_part fs`
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
   >-(xlet`POSTv v. W8ARRAY buf (1w::n2w n::h3::h4::rest) * IOx fs_ffi_part fs`
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
          (nr <= LENGTH content - pos) /\
          (nr = 0 ⇔ eof fd fs = SOME T ∨ n = 0)) *
        IOx fs_ffi_part (bumpFD fd fs nr) *
        W8ARRAY buf (0w :: n2w (nr DIV 256) :: n2w nr :: h4 ::
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
   simp[GSYM n2w2_def,w22n_n2w2] >> xsimpl >> gvs []
QED

(* TODO: call the low-level IOFS specs with the non-standard name, not vice versa *)

Theorem raw_input_IOFS_spec:
  !fd fdv fs content pos off offv.
    len + off <= LENGTH buf ∧
    INSTREAM fd fdv ∧ NUM off offv ∧ NUM len lenv ∧
    get_file_content fs fd = SOME(content, pos) ⇒
    get_mode fs fd = SOME ReadMode ⇒
    app (p:'ffi ffi_proj) TextIO_raw_input_v [fdv; bufv; offv; lenv]
    (IOFS fs * W8ARRAY bufv buf)
    (POSTv nv. &(NUM (MIN len (LENGTH content - pos)) nv) *
       W8ARRAY bufv (insert_atI (TAKE len (DROP pos (MAP (n2w o ORD) content)))
                                 off buf) *
       SEP_EXISTS k. IOFS (fsupdate fs fd k (MIN (len + pos) (MAX pos (LENGTH content))) content))
Proof
  rpt strip_tac >>
  xcf_with_def TextIO_raw_input_v_def >>
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
      \\ simp[AFUPDKEY_unchanged] )
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
        AFUPDKEY_unchanged,wfFS_def,liveFS_def,live_numchars_def]
     >-(fs[consistentFS_def] >> metis_tac[]) >>
     cases_on`fs'.numchars` >> fs[LDROP_1,NOT_LFINITE_DROP_LFINITE] >>
     cases_on`fs'.numchars` >> fs[LDROP_1] >> cases_on`fs`
     >-(qmatch_abbrev_tac`IOx _ fs1 ==>> IOx _ fs2 * GC` >>
     `fs1 = fs2` by (unabbrev_all_tac >>
                     fs[IO_fs_component_equality,AFUPDKEY_unchanged]) >>
     xsimpl) >>
     qmatch_abbrev_tac`IOx _ fs1 ==>> IOx _ fs2 * GC` >>
     `fs1 = fs2` by (unabbrev_all_tac >>
                     fs[IO_fs_component_equality,AFUPDKEY_unchanged]) >>
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
        AFUPDKEY_unchanged,wfFS_def,liveFS_def,live_numchars_def]
     >-(fs[consistentFS_def] >> metis_tac[]) >>
     cases_on`fs'.numchars` >> fs[LDROP_1,NOT_LFINITE_DROP_LFINITE] >>
     cases_on`fs'.numchars` >> fs[LDROP_1] >> cases_on`fs`
     >-(qmatch_abbrev_tac`IOx _ fs1 ==>> IOx _ fs2 * GC` >>
     `fs1 = fs2` by (unabbrev_all_tac >>
                     fs[IO_fs_component_equality,AFUPDKEY_unchanged]) >>
     xsimpl) >>
     qmatch_abbrev_tac`IOx _ fs1 ==>> IOx _ fs2 * GC` >>
     `fs1 = fs2` by (unabbrev_all_tac >>
                     fs[IO_fs_component_equality,AFUPDKEY_unchanged]) >>
     xsimpl) >>
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
      qexists_tac`fd,(ino, md,pos'')` >> fs[ALOOKUP_MEM]) >>
  xif
  >-(xvar >> xsimpl >> qexists_tac`1` >>
     fs[eof_def] >> pairarg_tac >> fs[get_file_content_def] >>
     pairarg_tac \\ fs[] \\ rveq \\
     `LENGTH content = pos'` by (fs[] >> rfs[]) >>
     fs[MIN_DEF,liveFS_fsupdate,insert_atI_NIL,bumpFD_def,AFUPDKEY_unchanged] >>
     rw[DROP_NIL] >- fs[validFD_def,wfFS_fsupdate]
     >- fs[GSYM MAP_DROP,DROP_LENGTH_NIL,insert_atI_NIL] >>
     qmatch_abbrev_tac `IOx _ fs1 ==>> IOx _ fs2 * GC` >>
     `fs1 = fs2` suffices_by xsimpl >>
     unabbrev_all_tac >> cases_on`fs'.numchars` >>
     fs[IO_fs_component_equality,AFUPDKEY_unchanged,fsupdate_def,LDROP_1,
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
     AFUPDKEY_ALOOKUP,INT_OF_NUM_SUBS_2,NUM_def,INT_def] >>
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
  fs[IO_fs_component_equality,AFUPDKEY_unchanged,fsupdate_def,LDROP_1] >>
  fs[AFUPDKEY_ALOOKUP,AFUPDKEY_o,AFUPDKEY_eq] >>
  simp[AFUPDKEY_unchanged])
  \\ xapp \\ instantiate \\ xsimpl
QED

Theorem raw_input_spec:
  !fd fdv fs content pos off offv len lenv buf bufv.
    len + off <= LENGTH buf ∧
    INSTREAM fd fdv ∧ NUM off offv ∧ NUM len lenv ∧
    get_file_content fs fd = SOME(content, pos) ⇒
    get_mode fs fd = SOME ReadMode ⇒
    app (p:'ffi ffi_proj) TextIO_raw_input_v [fdv; bufv; offv; lenv]
    (STDIO fs * W8ARRAY bufv buf)
    (POSTv nv. &(NUM (MIN len (LENGTH content - pos)) nv /\
       LENGTH buf = LENGTH (insert_atI (TAKE len (DROP pos (MAP (n2w o ORD) content)))
                                 off buf)) *
       W8ARRAY bufv (insert_atI (TAKE len (DROP pos (MAP (n2w o ORD) content)))
                                 off buf) *
        STDIO (fsupdate fs fd 0 (MIN (len + pos) (MAX pos (LENGTH content))) content))
Proof
  rw[STDIO_def]
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
  \\ fs[get_file_content_def, LENGTH_insert_atI, LENGTH_TAKE, LENGTH_TAKE_EQ]
  \\ xsimpl
QED

Theorem take_drop_append:
  x < LENGTH l /\ y < LENGTH l /\ z < LENGTH l  /\ ~(y<x) ==>
   TAKE x (DROP z l) ++ TAKE (y - x) (DROP (x+z) l) =
   TAKE y (DROP z l)
Proof
  fs[take_drop_partition,GSYM DROP_DROP_T]
QED

Theorem openStdInSetBufferSize_spec:
  ∀fs bsize bsizev bactive.
     NUM bsize bsizev ⇒
     app (p:'ffi ffi_proj) TextIO_openStdInSetBufferSize_v [bsizev]
       (IOFS fs)
       (POSTv is. INSTREAM_BUFFERED_FD [] 0 is * IOFS fs)
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_openStdInSetBufferSize_v_def
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet `POSTv wr1. REF_NUM wr1 4 *
                      (W8ARRAY v' (REPLICATE (MIN 65535 (MAX (bsize+4) 1028)) 48w)) *
                      IOFS fs`
  >-(xref \\ fs[REF_NUM_def, MIN_DEF] \\ xsimpl)
  \\ xlet `POSTv rr1. REF_NUM rr1 4 *
                        REF_NUM wr1 4 *
                        (W8ARRAY v' (REPLICATE (MIN 65535 (MAX (bsize+4) 1028)) 48w)) *
                        IOFS fs`
  >-(xref \\ fs[REF_NUM_def,MIN_DEF] \\ xsimpl)
  \\ xcon \\ fs[INSTREAM_BUFFERED_FD_def] \\ xsimpl
  \\ map_every qexists_tac [`4`, `4`]
  \\ fs[instream_buffered_inv_def,MAX_DEF] \\ xsimpl
  \\ fs[INSTREAM_def,GSYM raw_stdIn_def,raw_stdin_v_thm]
QED

Theorem openStdIn_spec:
  ∀fs uv.
    UNIT_TYPE () uv ⇒
    app (p:'ffi ffi_proj) TextIO_openStdIn_v [uv]
       (IOFS fs)
       (POSTv is. INSTREAM_BUFFERED_FD [] 0 is * IOFS fs)
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_openStdIn_v_def
  \\ xmatch \\ fs[UNIT_TYPE_def] \\ conj_tac
  >- (xapp \\ fs[INT_NUM_EXISTS])
  \\ EVAL_TAC \\ simp[]
QED

(* STDIO version *)
Theorem openStdIn_STDIO_spec:
   ∀uv fs.
     UNIT_TYPE () uv ⇒
     app (p:'ffi ffi_proj) TextIO_openStdIn_v [uv]
       (STDIO fs)
       (POSTv is. INSTREAM_BUFFERED_FD [] 0 is * STDIO fs)
Proof
 rw[STDIO_def] >> xpull >> xapp_spec openStdIn_spec >>
 map_every qexists_tac [`emp`,`fs with numchars := ll`] >>
 xsimpl >> rw[] >> qexists_tac`ll` >> fs[openFileFS_fupd_numchars] >> xsimpl
QED

Theorem openInSetBufferSize_spec:
  ∀s sv fs bsize bsizev bactive.
     FILENAME s sv ∧
     NUM bsize bsizev /\
     hasFreeFD fs ⇒
     app (p:'ffi ffi_proj) TextIO_openInSetBufferSize_v [sv;bsizev]
       (IOFS fs)
       (POSTve
          (\is. &(
                  validFD (nextFD fs) (openFileFS s fs ReadMode 0) ∧
                  inFS_fname fs s) *
                INSTREAM_BUFFERED_FD [] (nextFD fs) is *
                IOFS (openFileFS s fs ReadMode 0))
          (\e. &(BadFileName_exn e ∧ ~inFS_fname fs s)
                   * IOFS fs))
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_openInSetBufferSize_v_def
  \\ xlet_auto >- xsimpl >- (xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet `POSTv wr1. REF_NUM wr1 4 *
                      (W8ARRAY v'' (REPLICATE (MIN 65535 (MAX (bsize+4) 1028)) 48w)) *
                      IOFS (openFileFS s fs ReadMode 0)`
  >-(xref \\ fs[REF_NUM_def, MIN_DEF] \\ xsimpl)
  \\ xlet `POSTv rr1. REF_NUM rr1 4 *
                        REF_NUM wr1 4 *
                        (W8ARRAY v'' (REPLICATE (MIN 65535 (MAX (bsize+4) 1028)) 48w)) *
                        IOFS (openFileFS s fs ReadMode 0)`
  >-(xref \\ fs[REF_NUM_def,MIN_DEF] \\ xsimpl)
  \\ xcon \\ fs[INSTREAM_BUFFERED_FD_def] \\ xsimpl
  \\ map_every qexists_tac [`4`, `4`]
  \\ fs[instream_buffered_inv_def,MAX_DEF] \\ xsimpl
QED

Theorem openIn_spec:
  ∀s sv fs.
     FILENAME s sv ∧
     hasFreeFD fs ⇒
     app (p:'ffi ffi_proj) TextIO_openIn_v [sv]
       (IOFS fs)
       (POSTve
          (\is. &(
                  validFD (nextFD fs) (openFileFS s fs ReadMode 0) ∧
                  inFS_fname fs s) *
                INSTREAM_BUFFERED_FD [] (nextFD fs) is *
                IOFS (openFileFS s fs ReadMode 0))
          (\e. &(BadFileName_exn e ∧ ~inFS_fname fs s)
                   * IOFS fs))
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_openIn_v_def
  \\ xapp \\ fs[INT_NUM_EXISTS]
QED

(* STDIO version *)
Theorem openIn_STDIO_spec:
   ∀s sv fs.
     FILENAME s sv ∧
     hasFreeFD fs ⇒
     app (p:'ffi ffi_proj) TextIO_openIn_v [sv]
       (STDIO fs)
       (POSTve
          (\is. &(validFD (nextFD fs) (openFileFS s fs ReadMode 0) ∧
                  inFS_fname fs s) *
                INSTREAM_BUFFERED_FD [] (nextFD fs) is *
                STDIO (openFileFS s fs ReadMode 0))
          (\e. &(BadFileName_exn e ∧ ~inFS_fname fs s) * STDIO fs))
Proof
 rw[STDIO_def] >> xpull >> xapp_spec openIn_spec >>
 map_every qexists_tac [`emp`,`s`,`fs with numchars := ll`] >>
 xsimpl >> rw[] >> qexists_tac`ll` >> fs[openFileFS_fupd_numchars] >> xsimpl >>
 rw[] >>
 fs[nextFD_numchars,nextFD_numchars,openFileFS_fupd_numchars,STD_streams_openFileFS] >>
 fs[GSYM validFD_numchars,GSYM openFileFS_fupd_numchars,inFS_fname_numchars] \\ xsimpl
QED

Theorem closeIn_spec:
   ∀fd fs.
     app (p:'ffi ffi_proj) TextIO_closeIn_v [is]
       (IOFS fs * INSTREAM_BUFFERED_FD bactive fd is)
       (POSTve
          (\u. &(UNIT_TYPE () u /\ validFileFD fd fs.infds) *
               IOFS (fs with infds updated_by ADELKEY fd))
          (\e. &(InvalidFD_exn e /\ ¬ validFileFD fd fs.infds) * IOFS fs))
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_closeIn_v_def
  \\ simp[INSTREAM_BUFFERED_FD_def] \\ xpull \\ xmatch
  \\ xapp_spec raw_closeIn_spec \\ asm_exists_tac \\ CONV_TAC (SWAP_EXISTS_CONV)
  \\ qexists_tac `fs` \\ xsimpl
QED

Theorem closeIn_STDIO_spec:
   ∀fd fs.
     fd >= 3 /\ fd <= fs.maxFD ⇒
     app (p:'ffi ffi_proj) TextIO_closeIn_v [is]
       (STDIO fs * INSTREAM_BUFFERED_FD bactive fd is)
       (POSTve
          (\u. &(UNIT_TYPE () u /\ validFileFD fd fs.infds) *
               STDIO (fs with infds updated_by ADELKEY fd))
          (\e. &(InvalidFD_exn e /\ ¬ validFileFD fd fs.infds) * STDIO fs))
Proof
  rw[STDIO_def] >> xpull >> xapp_spec closeIn_spec >>
  map_every qexists_tac [`emp`,`fs with numchars := ll`,`fd`, `bactive`] >>
  xsimpl >> rw[] >> qexists_tac`ll` >> fs[validFileFD_def] >> xsimpl >>
  fs[STD_streams_def,ALOOKUP_ADELKEY] \\
  Cases_on`fd = 0` \\ fs[]
  \\ Cases_on`fd = 1` \\ fs[]
  \\ Cases_on`fd = 2` \\ fs[]
  \\ metis_tac[]
QED

Definition take_fromI_def:
  take_fromI n l i = TAKE n (DROP i l)
End

Theorem LENGTH_take_fromI:
  (n <= LENGTH l - i ==> LENGTH (take_fromI n l i) = n) /\
  (LENGTH l - i <= n ==> LENGTH (take_fromI n l i) = LENGTH l - i)
Proof
  fs[take_fromI_def, TAKE_LENGTH_TOO_LONG]
QED

Definition explode_fromI_def:
  explode_fromI n (content:string) pos =
      take_fromI n (MAP (n2w o ORD) content) pos :word8 list
End

Theorem LENGTH_explode_fromI:
  (n <= LENGTH l - i ==> LENGTH (explode_fromI n l i) = n) /\
  (LENGTH l - i <= n ==> LENGTH (explode_fromI n l i) = LENGTH l - i)
Proof
  fs[explode_fromI_def, LENGTH_take_fromI]
QED

Theorem refillBuffer_with_read_spec:
  !fd fdv fs content pos.
  is = (Conv instreambuffered_con_stamp [fdv; rr; wr; isbuff]) /\
  get_file_content fs fd = SOME(content, pos) ⇒
  get_mode fs fd = SOME ReadMode ⇒
  app (p:'ffi ffi_proj) TextIO_refillBuffer_with_read_v [is;]
  (IOFS fs * INSTREAM_BUFFERED_BL_FD bcontent bactive fd is )
  (POSTv wv. SEP_EXISTS (nr:num) h4 rest.
                 &(NUM nr wv /\
                   LENGTH bcontent =
                    LENGTH (0w::n2w (nr DIV 256)::n2w nr::h4::rest) /\
                   (nr = 0 ⇔ eof fd fs = SOME T) /\
                   (nr = 0 ⇔ ~(pos < STRLEN content)) /\
                   nr = LENGTH (explode_fromI nr content pos) /\
                   nr <= STRLEN content - pos) *
                 INSTREAM_BUFFERED_BL_FD
                    (0w::n2w (nr DIV 256)::n2w nr::h4::rest)
                    (explode_fromI nr content pos) fd is *
                 IOFS (bumpFD fd fs nr))
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_refillBuffer_with_read_v_def
  \\ fs[explode_fromI_def, take_fromI_def]
  \\ reverse(Cases_on`pos ≤ LENGTH content`)
    >-(imp_res_tac get_file_content_eof \\ rfs[]
      \\ fs[MAX_DEF, MIN_DEF, IOFS_def,
            INSTREAM_BUFFERED_BL_FD_def, instream_buffered_inv_def]
      \\ xpull \\ xmatch
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ fs[INSTREAM_def] \\ xlet_auto >- xsimpl
      \\ fs[get_in_def] \\ `FD fd sv` by fs[FD_def]
      \\ Cases_on `bcontent` >> fs[] >> qmatch_goalsub_rename_tac`h1::t`
      \\ Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::t`
      \\ Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::h3::t`
      \\ Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::h3::h4::t`
      \\ xlet_auto>- xsimpl \\ xsimpl \\ xsimpl
      \\ fs[REF_NUM_def] \\ xpull
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ xapp \\ xsimpl
      \\ qexists_tac `4` \\ rpt strip_tac >- fs[NUM_def]
      \\ fs[NUM_def]
      \\ map_every qexists_tac [`4`] \\ fs[])
    >-(imp_res_tac get_file_content_eof \\ rfs[]
      \\ fs[IOFS_def,
            INSTREAM_BUFFERED_BL_FD_def, instream_buffered_inv_def]
      \\ xpull \\ xmatch
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ fs[INSTREAM_def] \\ xlet_auto >- xsimpl
      \\ fs[get_in_def] \\ `FD fd sv` by fs[FD_def]
      \\ Cases_on `bcontent` >> fs[] >> qmatch_goalsub_rename_tac`h1::t`
      \\ Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::t`
      \\ Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::h3::t`
      \\ Cases_on `t` >> fs[] >> qmatch_goalsub_rename_tac`h1::h2::h3::h4::t`
      \\ xlet_auto
      >-(xsimpl \\ rpt strip_tac \\ qexists_tac `x` \\ xsimpl) \\ xsimpl
      \\ xlet_auto >- xsimpl
      \\ fs[REF_NUM_def] \\ xpull
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ xapp \\ xsimpl \\ fs[NUM_def]
      \\ qexists_tac `&(nr + 4)` \\ fs[] \\ rpt strip_tac
      \\ qabbrev_tac `buff_size = SUC (SUC (SUC (SUC (LENGTH t))))`
      \\ map_every qexists_tac [`nr`,`&(nr+4)`] \\ xsimpl
      \\ fs[INT_SUB_CALCULATE, INT_ADD_CALCULATE]
      \\ fs[MAP_TAKE, TAKE_APPEND1, MAP_DROP, TAKE_TAKE])
QED

val eq_v_thm = fetch "mlbasicsProg" "eq_v_thm";
val eq_num_v_thm = MATCH_MP (DISCH_ALL eq_v_thm) (EqualityType_NUM_BOOL |> CONJUNCT1);

val neq_v_thm = fetch "mlbasicsProg" "neq_v_thm";
val neq_char_v_thm = MATCH_MP (DISCH_ALL neq_v_thm)
  (EqualityType_NUM_BOOL |> CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2);

Theorem input1_aux_spec:
  app (p:'ffi ffi_proj) TextIO_input1_aux_v [is]
  (INSTREAM_BUFFERED_BL_FD_RW bcontent bactive fd r w is)
  (POSTv chv. SEP_EXISTS cs.
    case bactive of
      [] =>
        &(OPTION_TYPE CHAR NONE chv) *
        INSTREAM_BUFFERED_BL_FD_RW bcontent bactive fd r w is
      |(c::cs) =>
        &OPTION_TYPE CHAR (SOME ((CHR o w2n) c)) chv *
        INSTREAM_BUFFERED_BL_FD_RW bcontent cs fd (r + 1) w is)
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_input1_aux_v_def
  \\ fs[INSTREAM_BUFFERED_BL_FD_RW_def, REF_NUM_def] \\ xpull
  \\ xmatch \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet `POSTv bv. & (BOOL (w = r) bv) *
              INSTREAM_BUFFERED_BL_FD_RW bcontent bactive fd r w is`
  >-(xapp_spec eq_num_v_thm \\ fs[INT_NUM_EXISTS]
    \\ CONV_TAC (SWAP_EXISTS_CONV) \\ rpt (asm_exists_tac \\ xsimpl)
    \\ simp[INSTREAM_BUFFERED_BL_FD_RW_def, REF_NUM_def]
    \\ xsimpl \\ rpt strip_tac \\ asm_exists_tac \\ xsimpl)
  \\ xif
  >-(fs[INSTREAM_BUFFERED_BL_FD_RW_def, REF_NUM_def, instream_buffered_inv_def]
    \\ xpull \\ xcon \\ `r = w` by fs[]
    \\ `TAKE (w − r) (DROP r bcontent) = []` by fs[LENGTH_TAKE]
    \\ rw[]
    >-(xsimpl \\ fs[std_preludeTheory.OPTION_TYPE_def]))
  >-(simp[INSTREAM_BUFFERED_BL_FD_RW_def, REF_NUM_def] \\ xpull
    \\ gvs[]
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- (xsimpl \\ fs[instream_buffered_inv_def])
    \\ xlet_auto >- xsimpl \\ fs [(*CharProgTheory.fromByte_def*)]
    \\ xapp
    \\ `bactive <> []` by (fs[instream_buffered_inv_def] \\ fs[DROP_NIL])
    \\ xsimpl
    \\ asm_exists_tac \\ fs [CharProgTheory.some_char_thm]
    \\ CASE_TAC
    >-(fs[])
    >-(xsimpl
      \\ fs[instream_buffered_inv_def, std_preludeTheory.OPTION_TYPE_def] \\ xsimpl
      \\ ntac 2 strip_tac \\ fs []
      \\ reverse conj_tac
      >-(`h::t = (TAKE (w − r) (DROP r bcontent))` by fs[]
        \\ `t = DROP 1 (TAKE (w − r) (DROP r bcontent))`
            by (Cases_on `(TAKE (w − r) (DROP r bcontent))`
                >-fs[]
                >-(`t' = t` by fs[] \\ EVAL_TAC \\ fs[]))
        \\ fs[DROP_SEG, TAKE_SEG, SEG_SEG])
      >-(`[h] = TAKE 1 (TAKE (w-r) (DROP r bcontent))`
            by (`h::t = (TAKE (w − r) (DROP r bcontent))` by fs[]
                \\ Cases_on `(TAKE (w − r) (DROP r bcontent))`
                >-fs[DROP_NIL]
                >-(`h' = h` by fs[]
                  \\ fs[TAKE]))
        \\ `1 <= w-r`
            by (Cases_on `(TAKE (w − r) (DROP r bcontent))`
                >-fs[]
                >-fs[LENGTH_TAKE, NOT_NIL_EQ_LENGTH_NOT_0])
        \\ `[h] = TAKE 1 (DROP r bcontent)` by fs[LENGTH_TAKE,TAKE_TAKE]
        \\ `r < LENGTH bcontent` by fs[]
        \\ `[EL r bcontent] = TAKE 1 (DROP r bcontent)` by fs[TAKE1_DROP]
        \\ Cases_on `TAKE 1 (DROP r bcontent)`
        >-fs[]
        >-(`h = h'` by fs[]
          \\ `EL r bcontent = h` by fs[] \\ fs[]))))
QED

Theorem peekChar_aux_spec:
  app (p:'ffi ffi_proj) TextIO_peekChar_aux_v [is]
  (INSTREAM_BUFFERED_BL_FD_RW bcontent bactive fd r w is)
  (POSTv chv. SEP_EXISTS cs.
    case bactive of
      [] =>
        &(OPTION_TYPE CHAR NONE chv) *
        INSTREAM_BUFFERED_BL_FD_RW bcontent bactive fd r w is
      |(c::cs) =>
        &OPTION_TYPE CHAR (SOME ((CHR o w2n) c)) chv *
        INSTREAM_BUFFERED_BL_FD_RW bcontent bactive fd r w is)
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_peekChar_aux_v_def
  \\ fs[INSTREAM_BUFFERED_BL_FD_RW_def, REF_NUM_def] \\ xpull
  \\ xmatch \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet `POSTv bv. & (BOOL (w = r) bv) *
              INSTREAM_BUFFERED_BL_FD_RW bcontent bactive fd r w is`
  >-(xapp_spec eq_num_v_thm \\ fs[INT_NUM_EXISTS]
    \\ CONV_TAC (SWAP_EXISTS_CONV) \\ rpt (asm_exists_tac \\ xsimpl)
    \\ simp[INSTREAM_BUFFERED_BL_FD_RW_def, REF_NUM_def]
    \\ xsimpl \\ rpt strip_tac \\ asm_exists_tac \\ xsimpl)
  \\ xif
  >-(fs[INSTREAM_BUFFERED_BL_FD_RW_def, REF_NUM_def, instream_buffered_inv_def]
    \\ xpull \\ xcon \\ `r = w` by fs[]
    \\ `TAKE (w − r) (DROP r bcontent) = []` by fs[LENGTH_TAKE]
    \\ rw[]
    >-(xsimpl \\ fs[std_preludeTheory.OPTION_TYPE_def]))
  >-(simp[INSTREAM_BUFFERED_BL_FD_RW_def, REF_NUM_def] \\ xpull
    \\ xlet_auto >- xsimpl
    \\ rveq
    \\ xlet_auto >- (xsimpl \\ fs[instream_buffered_inv_def])
    \\ xlet_auto >- xsimpl \\ fs [(* CharProgTheory.fromByte_def *)]
    \\ xapp
    \\ `bactive <> []` by (fs[instream_buffered_inv_def] \\ fs[DROP_NIL])
    \\ xsimpl
    \\ asm_exists_tac \\ fs [CharProgTheory.some_char_thm]
    \\ CASE_TAC
    >-(fs[])
    >-(xsimpl
      \\ fs[instream_buffered_inv_def, std_preludeTheory.OPTION_TYPE_def] \\ xsimpl
      \\ ntac 2 strip_tac \\ fs []
      \\ `[h] = TAKE 1 (TAKE (w-r) (DROP r bcontent))`
            by (`h::t = (TAKE (w − r) (DROP r bcontent))` by fs[]
                \\ Cases_on `(TAKE (w − r) (DROP r bcontent))`
                >-fs[DROP_NIL]
                >-(`h' = h` by fs[]
                  \\ fs[TAKE]))
       \\ `1 <= w-r`
         by (Cases_on `(TAKE (w − r) (DROP r bcontent))`
             >-fs[]
             >-fs[LENGTH_TAKE, NOT_NIL_EQ_LENGTH_NOT_0])
       \\ `[h] = TAKE 1 (DROP r bcontent)` by fs[LENGTH_TAKE,TAKE_TAKE]
       \\ `r < LENGTH bcontent` by fs[]
       \\ `[EL r bcontent] = TAKE 1 (DROP r bcontent)` by fs[TAKE1_DROP]
       \\ Cases_on `TAKE 1 (DROP r bcontent)`
       >-fs[]
       >-(`h = h'` by fs[]
          \\ `EL r bcontent = h` by fs[] \\ fs[])))
QED

Theorem DROP_TAKE:
  !xs k n. DROP k (TAKE n xs) = TAKE (n - k) (DROP k xs)
Proof
  Induct \\ fs [DROP_def,TAKE_def] \\ rw []
QED

Theorem TAKE_DROP_EQ_CONS_IMP:
  !n pos xs y ys.
    TAKE n (DROP pos xs) = y::ys ==>
    TAKE (n-1) (DROP (pos+1) xs) = ys
Proof
  Induct_on `xs` \\ fs [TAKE_def,DROP_def] \\ rw []
  THEN1 (Cases_on `n` \\ fs [TAKE_def])
  \\ res_tac \\ fs []
  \\ pop_assum mp_tac
  \\ `pos - 1 + 1 = pos` by fs []
  \\ asm_rewrite_tac []
QED

Theorem input1_IOFS_spec:
  !fd fdv fs content pos bactive.
  get_file_content fs fd = SOME(content, pos) ⇒
  get_mode fs fd = SOME ReadMode ⇒
  app (p:'ffi ffi_proj) TextIO_input1_v [is]
     (IOFS fs * INSTREAM_BUFFERED_FD bactive fd is)
     (POSTv chv.
       case bactive of
       | (c::cs) => &(OPTION_TYPE CHAR (SOME ((CHR o w2n) c)) chv) *
                    IOFS fs * INSTREAM_BUFFERED_FD cs fd is
       | [] =>
           if LENGTH content <= pos then
             &(OPTION_TYPE CHAR NONE chv) *
             IOFS (bumpFD fd fs 0) * INSTREAM_BUFFERED_FD [] fd is
           else
             SEP_EXISTS leftover.
               &(OPTION_TYPE CHAR (SOME (EL pos content)) chv) *
               IOFS (bumpFD fd fs (LENGTH leftover + 1)) *
               INSTREAM_BUFFERED_FD leftover fd is *
               &(leftover = explode_fromI (LENGTH leftover) content (pos + 1) /\
                (pos + LENGTH leftover + 1 <= STRLEN content)))
Proof
    rpt strip_tac
    \\ xcf_with_def TextIO_input1_v_def
    \\ simp[INSTREAM_BUFFERED_FD_def, REF_NUM_def, instream_buffered_inv_def]
    \\ xpull
    \\ xmatch
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet `POSTv bv. & (BOOL (w = r) bv) * IOFS fs
              * INSTREAM_BUFFERED_BL_FD bcontent
                  bactive fd is`
      >- ( xapp_spec eq_num_v_thm
        \\ xsimpl
        \\ qexists_tac `r` \\ qexists_tac `w`
        \\ `NUM w yv' /\ NUM r yv` by (rveq \\ fs[]) \\ simp[]
        \\ fs[INSTREAM_BUFFERED_BL_FD_def,NUM_def, INT_def, BOOL_def, REF_NUM_def,
              instream_buffered_inv_def]
        \\ xsimpl)
    \\ xif
    >-(xlet `POSTv dc.
              SEP_EXISTS (nr:num) h4 rest.
                &((nr = 0 ⇔ STRLEN content <= pos) /\
                  LENGTH bcontent = LENGTH (0w::n2w (nr DIV 256)::n2w nr::h4::rest) /\
                  nr = LENGTH (explode_fromI nr content pos) /\
                  nr <= STRLEN content - pos) *
                IOFS
                    (bumpFD fd fs nr) *
                INSTREAM_BUFFERED_BL_FD
                  (0w::n2w (nr DIV 256)::n2w nr::h4::rest)
                  (explode_fromI nr content pos) fd is`
      >-(simp[Once INSTREAM_BUFFERED_BL_FD_def, REF_NUM_def, instream_buffered_inv_def]
        \\ xpull \\ xapp \\ xsimpl \\ CONV_TAC(RESORT_EXISTS_CONV List.rev) \\ asm_exists_tac
        \\ map_every qexists_tac [`bactive`,
                                  `bcontent`, `content`,`pos`] \\ xsimpl
        \\ simp[Once INSTREAM_BUFFERED_BL_FD_def, REF_NUM_def, instream_buffered_inv_def]
        \\ xsimpl \\ fs[PULL_EXISTS] \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
        \\ map_every qexists_tac [`w'`,`r'`] \\ xsimpl
        \\ rpt strip_tac \\ map_every qexists_tac [`x`,`x'`,`x''`]
        \\ simp[GSYM take_fromI_def]\\ simp[GSYM explode_fromI_def] \\ xsimpl)
      \\ simp[INSTREAM_BUFFERED_BL_FD_def, REF_NUM_def, instream_buffered_inv_def]
      \\ xpull \\ xapp \\ xsimpl
      \\ simp[Once INSTREAM_BUFFERED_BL_FD_RW_def, REF_NUM_def]
      \\ xsimpl \\ fs[PULL_EXISTS] \\ CONV_TAC (RESORT_EXISTS_CONV List.rev)
      \\ asm_exists_tac \\ map_every qexists_tac
                            [`explode_fromI nr content pos`,`r'`,`w'`]
      \\ xsimpl \\ simp[instream_buffered_inv_def] \\ rpt strip_tac
      \\ `TAKE (w' − r') (DROP r' (0w::n2w (nr DIV 256)::n2w nr::h4::rest)) =
          TAKE (w' − r') (DROP (r' − 4) rest)` by fs[]
      \\ CASE_TAC
      >-(cases_on `0 < nr`
        >-(fs[explode_fromI_def, take_fromI_def,
                LENGTH_TAKE, NOT_NIL_EQ_LENGTH_NOT_0, DROP_NIL])
        >-(simp[INSTREAM_BUFFERED_BL_FD_RW_def, REF_NUM_def] \\ xsimpl
          \\ rpt strip_tac \\ map_every qexists_tac [`r'`, `w'`]
          \\ `nr = 0` by fs[] \\ `w' - r' = 0` by fs[] \\ xsimpl
          \\ fs[instream_buffered_inv_def, LENGTH_explode_fromI]
          \\ xsimpl))
      >-(xsimpl \\ rpt strip_tac \\ fs[instream_buffered_inv_def]
        \\ xsimpl \\ fs[NUM_def, INT_def,INT_NUM_EXISTS]
        \\ simp[INSTREAM_BUFFERED_BL_FD_RW_def, REF_NUM_def]
        \\ xsimpl \\ fs[NUM_def, INT_def,INT_NUM_EXISTS, instream_buffered_inv_def]
        \\ `t = DROP 1 (TAKE (w' − r') (DROP (r' − 4) rest))` by fs[]
        \\ rw[] \\ simp[TAKE_SEG, DROP_SEG, SEG_SEG]
        \\ fs[explode_fromI_def, take_fromI_def] \\ xsimpl
        \\ conj_tac
        >-(qabbrev_tac `bytes = (DROP pos (MAP (n2w ∘ ORD) content)) : word8 list`
          \\ `[h] = TAKE 1 (TAKE (w' − r') bytes)`
                by fs[Abbr`bytes`]
          \\ `1 <= (w' − r')` by fs[]
          \\ `[h] = TAKE 1 bytes`
                by fs[Abbr`bytes`,TAKE_TAKE_T]
          \\ `bytes <> []`
                by fs[Abbr`bytes`,LENGTH_DROP, LENGTH_TAKE, DROP_NIL]
          \\ `h:word8 = EL 0 bytes` by fs[TAKE1]
          \\ `0 + pos < LENGTH (MAP (n2w ∘ ORD) content)` by fs[Abbr`bytes`]
          \\ `h = EL pos (MAP (n2w ∘ ORD) content)` by fs[Abbr`bytes`, EL_DROP]
          \\ `h = (n2w o ORD) (EL pos content)` by fs[EL_MAP]
          \\ `h = n2w (ORD (EL pos content))` by fs[o_THM]
          \\ qpat_x_assum `h = EL pos _` kall_tac \\ qpat_x_assum `h = EL 0 _` kall_tac
          \\ qpat_x_assum `h = (n2w o ORD) _` kall_tac \\ rw[]
          \\ fs[CHR_w2n_n2w_ORD_simp])
        >-(simp[SEG_TAKE_DROP]
          \\ fs [GSYM NOT_LESS]
          \\ qpat_x_assum `TAKE (w' − r') (DROP pos (MAP (n2w ∘ ORD) content)) = _ :: _`
                 assume_tac
          \\ drule TAKE_DROP_EQ_CONS_IMP \\ rewrite_tac [GSYM SUB_PLUS]
          \\ simp_tac std_ss [rich_listTheory.DROP_DROP_T,DROP_TAKE]
          \\ simp [])))
    >-(simp[INSTREAM_BUFFERED_BL_FD_def, REF_NUM_def] \\ xpull
      \\ xapp \\ xsimpl
      \\ qexists_tac `IOFS fs`
      \\ simp[INSTREAM_BUFFERED_BL_FD_RW_def, REF_NUM_def]
      \\ CONV_TAC (RESORT_EXISTS_CONV List.rev) \\ xsimpl
      \\ asm_exists_tac \\ map_every qexists_tac [`bactive`,
                            `r'`,`w'`] \\ fs[]
      \\ rpt strip_tac
      \\ CASE_TAC
      >-(fs[])
      >-(xsimpl \\ rpt strip_tac \\ map_every qexists_tac [`r' + 1`, `w'`]
        \\ fs[instream_buffered_inv_def]))
QED

Theorem peekChar_IOFS_spec:
  !fd fdv fs content pos bactive.
  get_file_content fs fd = SOME(content, pos) ⇒
  get_mode fs fd = SOME ReadMode ⇒
  app (p:'ffi ffi_proj) TextIO_peekChar_v [is]
     (IOFS fs * INSTREAM_BUFFERED_FD bactive fd is)
     (POSTv chv.
       case bactive of
       | (c::cs) => &(OPTION_TYPE CHAR (SOME ((CHR o w2n) c)) chv) *
                    IOFS fs * INSTREAM_BUFFERED_FD bactive fd is
       | [] =>
           if LENGTH content <= pos then
             &(OPTION_TYPE CHAR NONE chv) *
             IOFS (bumpFD fd fs 0) * INSTREAM_BUFFERED_FD bactive fd is
           else
             SEP_EXISTS leftover.
               &(OPTION_TYPE CHAR (SOME (EL pos content)) chv) *
               IOFS (bumpFD fd fs (LENGTH leftover)) *
               INSTREAM_BUFFERED_FD leftover fd is *
               &(leftover = explode_fromI (LENGTH leftover) content pos /\
                (pos + LENGTH leftover <= STRLEN content)))
Proof
    rpt strip_tac
    \\ xcf_with_def TextIO_peekChar_v_def
    \\ simp[INSTREAM_BUFFERED_FD_def, REF_NUM_def, instream_buffered_inv_def]
    \\ xpull
    \\ xmatch
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet `POSTv bv. & (BOOL (w = r) bv) *
              IOFS fs
              * INSTREAM_BUFFERED_BL_FD_RW bcontent
                  bactive fd r w is`
      >- ( xapp_spec eq_num_v_thm
        \\ xsimpl
        \\ `NUM w yv' /\ NUM r yv` by (rveq \\ fs[]) \\ simp[]
        \\ fs[INSTREAM_BUFFERED_BL_FD_RW_def,NUM_def, INT_def, BOOL_def, REF_NUM_def,
              instream_buffered_inv_def]
        \\ xsimpl)
    \\ xif
    >-(xlet `POSTv dc.
              SEP_EXISTS (nr:num) h4 rest.
                &((nr = 0 ⇔ STRLEN content <= pos) /\
                  LENGTH bcontent = LENGTH (0w::n2w (nr DIV 256)::n2w nr::h4::rest) /\
                  nr = LENGTH (explode_fromI nr content pos) /\
                  nr <= STRLEN content - pos) *
                IOFS
                    (bumpFD fd fs nr) *
                INSTREAM_BUFFERED_BL_FD
                  (0w::n2w (nr DIV 256)::n2w nr::h4::rest)
                  (explode_fromI nr content pos) fd is`
      >-(simp[Once INSTREAM_BUFFERED_BL_FD_RW_def, REF_NUM_def, instream_buffered_inv_def]
        \\ xpull \\ xapp \\ xsimpl \\ CONV_TAC(RESORT_EXISTS_CONV List.rev) \\ asm_exists_tac
        \\ map_every qexists_tac [`bactive`,
                                  `bcontent`, `content`,`pos`] \\ xsimpl
        \\ simp[Once INSTREAM_BUFFERED_BL_FD_def, REF_NUM_def, instream_buffered_inv_def]
        \\ xsimpl \\ fs[PULL_EXISTS] \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
        \\ map_every qexists_tac [`w`,`r`] \\ xsimpl \\ fs []
        \\ rpt strip_tac \\ map_every qexists_tac [`x`,`x'`,`x''`]
        \\ simp[GSYM take_fromI_def]\\ simp[GSYM explode_fromI_def] \\ xsimpl)
      \\ simp[INSTREAM_BUFFERED_BL_FD_def, REF_NUM_def, instream_buffered_inv_def]
      \\ xpull \\ xapp \\ xsimpl
      \\ simp[Once INSTREAM_BUFFERED_BL_FD_RW_def, REF_NUM_def]
      \\ xsimpl \\ fs[PULL_EXISTS] \\ CONV_TAC (RESORT_EXISTS_CONV List.rev)
      \\ asm_exists_tac \\ map_every qexists_tac
                            [`explode_fromI nr content pos`,`r'`,`w'`]
      \\ xsimpl \\ simp[instream_buffered_inv_def] \\ rpt strip_tac
      \\ `TAKE (w' − r') (DROP r' (0w::n2w (nr DIV 256)::n2w nr::h4::rest)) =
          TAKE (w' − r') (DROP (r' − 4) rest)` by fs[]
      \\ CASE_TAC
      >-(cases_on `0 < nr`
        >-(fs[explode_fromI_def, take_fromI_def,
                LENGTH_TAKE, NOT_NIL_EQ_LENGTH_NOT_0, DROP_NIL])
        >-(simp[INSTREAM_BUFFERED_BL_FD_RW_def, REF_NUM_def] \\ xsimpl
          \\ rpt strip_tac \\ map_every qexists_tac [`r'`, `w'`]
          \\ `nr = 0` by fs[] \\ `w' - r' = 0` by fs[] \\ xsimpl
          \\ fs[instream_buffered_inv_def, LENGTH_explode_fromI]
          \\ xsimpl))
       >-(xsimpl \\ rpt strip_tac \\ fs[instream_buffered_inv_def]
          \\ xsimpl \\ fs[NUM_def, INT_def,INT_NUM_EXISTS]
          \\ simp[INSTREAM_BUFFERED_BL_FD_RW_def, REF_NUM_def]
          \\ xsimpl \\ fs[NUM_def, INT_def,INT_NUM_EXISTS, instream_buffered_inv_def]
          \\ xsimpl
          \\ `t = DROP 1 (TAKE (w' − r') (DROP (r' − 4) rest))` by fs[]
          \\ rw[] \\ simp[TAKE_SEG, DROP_SEG, SEG_SEG]
          \\ fs[explode_fromI_def, take_fromI_def] \\ xsimpl
          \\ qabbrev_tac `bytes = (DROP pos (MAP (n2w ∘ ORD) content)) : word8 list`
          \\ `[h] = TAKE 1 (TAKE (w' − r') bytes)`
            by fs[Abbr`bytes`]
          \\ `1 <= (w' − r')` by fs[]
          \\ `[h] = TAKE 1 bytes`
            by fs[Abbr`bytes`,TAKE_TAKE_T]
          \\ `bytes <> []`
            by fs[Abbr`bytes`,LENGTH_DROP, LENGTH_TAKE, DROP_NIL]
          \\ `h:word8 = EL 0 bytes` by fs[TAKE1]
          \\ `0 + pos < LENGTH (MAP (n2w ∘ ORD) content)` by fs[Abbr`bytes`]
          \\ `h = EL pos (MAP (n2w ∘ ORD) content)` by fs[Abbr`bytes`, EL_DROP]
          \\ `h = (n2w o ORD) (EL pos content)` by fs[EL_MAP]
          \\ `h = n2w (ORD (EL pos content))` by fs[o_THM]
          \\ qpat_x_assum `h = EL pos _` kall_tac \\ qpat_x_assum `h = EL 0 _` kall_tac
          \\ qpat_x_assum `h = (n2w o ORD) _` kall_tac \\ rw[]
          \\ fs[CHR_w2n_n2w_ORD_simp]))
    \\ xapp \\ xsimpl
    \\ qexists_tac `IOFS fs`
    \\ CONV_TAC (RESORT_EXISTS_CONV List.rev) \\ xsimpl
    \\ qexists_tac ‘bactive’ \\ fs []
    \\ qexists_tac ‘bcontent’ \\ fs []
    \\ qexists_tac ‘fd’ \\ fs []
    \\ qexists_tac ‘r’ \\ fs []
    \\ qexists_tac ‘w’ \\ fs []
    \\ xsimpl
    \\ CASE_TAC
    >-(fs[])
    \\ fs [INSTREAM_BUFFERED_BL_FD_RW_def,REF_NUM_def]
    \\ xsimpl \\ rpt strip_tac
    \\ gvs []
    \\ qpat_x_assum ‘_ = _::_’ $ irule_at Any o GSYM \\ fs []
    \\ first_assum $ irule_at $ Pos hd \\ fs []
    \\ fs [NUM_def,INT_def]
QED

Theorem input1_spec:
  !fd fdv fs content pos bactive.
  get_file_content fs fd = SOME(content, pos) ⇒
  get_mode fs fd = SOME ReadMode ⇒
  app (p:'ffi ffi_proj) TextIO_input1_v [is]
     (STDIO fs * INSTREAM_BUFFERED_FD bactive fd is)
     (POSTv chv.
       case bactive of
       | (c:word8::cs) => &(OPTION_TYPE CHAR (SOME ((CHR o w2n) c)) chv) *
                    STDIO fs * INSTREAM_BUFFERED_FD cs fd is
       | [] =>
           if LENGTH content <= pos then
             &(OPTION_TYPE CHAR NONE chv) *
             STDIO (bumpFD fd fs 0) * INSTREAM_BUFFERED_FD [] fd is
           else
             SEP_EXISTS leftover.
               &(OPTION_TYPE CHAR (SOME (EL pos content)) chv) *
               STDIO (bumpFD fd fs (LENGTH leftover + 1)) *
               INSTREAM_BUFFERED_FD leftover fd is *
               &(leftover = explode_fromI (LENGTH leftover) content (pos + 1) /\
                pos + LENGTH leftover + 1 <= STRLEN content))
Proof
  rw[STDIO_def]
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
  \\ simp[STD_streams_bumpFD, STD_streams_forwardFD]
  \\ xapp_spec input1_IOFS_spec
  \\ mp_tac(SYM (SPEC_ALL get_file_content_numchars)) \\ rw[]
  \\ mp_tac(get_mode_with_numchars) \\ rw[]
  \\ instantiate \\ xsimpl
  \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
  \\ qexists_tac `bactive` \\ xsimpl \\ rpt strip_tac
  \\ simp[bumpFD_forwardFD] \\ simp[STD_streams_forwardFD]
  \\ fs[forwardFD_def, IOFS_def, IOx_def,
        IO_fs_component_equality,AFUPDKEY_unchanged,AFUPDKEY_eq]
  \\ fs[get_file_content_def, LENGTH_insert_atI, LENGTH_TAKE, LENGTH_TAKE_EQ]
  \\ CASE_TAC
  >-(CASE_TAC
    >-(xsimpl \\ rpt strip_tac \\ qexists_tac`THE (LTL ll)` \\ xsimpl)
    >-(xsimpl \\ rpt strip_tac \\ qexists_tac`ll` \\ xsimpl))
  >-(xsimpl \\ CASE_TAC
    >-(xsimpl \\ rpt strip_tac \\ qexists_tac `x'` \\ qexists_tac`THE (LTL ll)` \\ xsimpl)
    >-(xsimpl \\ rpt strip_tac \\ qexists_tac`ll` \\ xsimpl))
QED

Theorem peekChar_spec:
  !fd fdv fs content pos bactive.
  get_file_content fs fd = SOME(content, pos) ⇒
  get_mode fs fd = SOME ReadMode ⇒
  app (p:'ffi ffi_proj) TextIO_peekChar_v [is]
     (STDIO fs * INSTREAM_BUFFERED_FD bactive fd is)
     (POSTv chv.
       case bactive of
       | (c:word8::cs) => &(OPTION_TYPE CHAR (SOME ((CHR o w2n) c)) chv) *
                          STDIO fs * INSTREAM_BUFFERED_FD bactive fd is
       | [] =>
           if LENGTH content <= pos then
             &(OPTION_TYPE CHAR NONE chv) *
             STDIO (bumpFD fd fs 0) * INSTREAM_BUFFERED_FD [] fd is
           else
             SEP_EXISTS leftover.
               &(OPTION_TYPE CHAR (SOME (EL pos content)) chv) *
               STDIO (bumpFD fd fs (LENGTH leftover)) *
               INSTREAM_BUFFERED_FD leftover fd is *
               &(leftover = explode_fromI (LENGTH leftover) content pos /\
                pos + LENGTH leftover <= STRLEN content))
Proof
  rw[STDIO_def]
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
  \\ simp[STD_streams_bumpFD, STD_streams_forwardFD]
  \\ xapp_spec peekChar_IOFS_spec
  \\ mp_tac(SYM (SPEC_ALL get_file_content_numchars)) \\ rw[]
  \\ mp_tac(get_mode_with_numchars) \\ rw[]
  \\ instantiate \\ xsimpl
  \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
  \\ qexists_tac `bactive` \\ xsimpl \\ rpt strip_tac
  \\ simp[bumpFD_forwardFD] \\ simp[STD_streams_forwardFD]
  \\ fs[forwardFD_def, IOFS_def, IOx_def,
        IO_fs_component_equality,AFUPDKEY_unchanged,AFUPDKEY_eq]
  \\ fs[get_file_content_def, LENGTH_insert_atI, LENGTH_TAKE, LENGTH_TAKE_EQ]
  \\ CASE_TAC
  >-(CASE_TAC
    >-(xsimpl \\ rpt strip_tac \\ qexists_tac`THE (LTL ll)` \\ xsimpl)
    >-(xsimpl \\ rpt strip_tac \\ qexists_tac`ll` \\ xsimpl))
  >-(xsimpl \\ CASE_TAC
    >-(xsimpl \\ rpt strip_tac \\ qexists_tac `x'` \\ qexists_tac`THE (LTL ll)` \\ xsimpl)
    >-(xsimpl \\ rpt strip_tac \\ qexists_tac`ll` \\ xsimpl))
QED

Definition takeUntilIncl_def:
  ((takeUntilIncl p [] = []) /\
  takeUntilIncl p (x::xs) = if p x then [x] else (x::takeUntilIncl p xs))
End

Definition dropUntilIncl_def:
  dropUntilIncl p l = DROP 1 (dropUntil p l)
End

Theorem dropUntil_drop_drop:
  !P  l x.
      EVERY ($~ o P) (TAKE x l) ==>
        dropUntil P l = dropUntil P (DROP x l)
Proof
  strip_tac
  \\ Induct
    >- ( simp[] )
    >- ( rpt strip_tac
      \\ cases_on `P h`
        >- (
         cases_on `x`
          >- (  simp[] )
          >- ( fs[every_def]))
        >- (
          cases_on `x`
            >- ( simp[] )
            >- (  simp[DROP]
              \\ cases_on `LENGTH l ≤ n`
                >- ( cases_on `dropUntil P l`
                  >- ( simp[DROP_LENGTH_TOO_LONG] \\ simp[mllistTheory.dropUntil_def])
                  >- ( fs[mllistTheory.dropUntil_def] ))
                >- ( fs[mllistTheory.dropUntil_def] )
             )
          )
      )
QED

Theorem dropUntilIncl_drop_drop:
  !P  l x.
      EVERY ($~ o P) (TAKE x l) ==>
        dropUntilIncl P l = dropUntilIncl P (DROP x l)
Proof
  strip_tac \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[dropUntilIncl_def])
  >-(Cases_on `0 < x`
    >-(`~P h` by fs[EVERY_DEF, TAKE]
      \\ simp[dropUntilIncl_def, mllistTheory.dropUntil_def]
      \\ fs[GSYM dropUntilIncl_def])
    >-(fs[DROP_0]))
QED

Theorem takeUntil_length_cons:
  !P  l x.
      ($~ o P) h ==>
        LENGTH (takeUntil P (h::t)) = SUC (LENGTH (takeUntil P t))
Proof
    rpt strip_tac
    \\ simp[mllistTheory.takeUntil_def]
    \\ CASE_TAC
    >-fs[]
    >-simp[]
QED

Theorem takeUntilIncl_length_cons:
  !P  l x.
      ($~ o P) h ==>
        LENGTH (takeUntilIncl P (h::t)) = SUC (LENGTH (takeUntilIncl P t))
Proof
    rpt strip_tac
    \\ simp[takeUntilIncl_def]
    \\ CASE_TAC
    >-fs[]
    >-simp[]
QED

Theorem takeUntil_cons:
  !P  l x.
      ($~ o P) h ==>
        takeUntil P (h::t) = h :: takeUntil P t
Proof
  rpt strip_tac
  \\ simp[mllistTheory.takeUntil_def]
  \\ CASE_TAC
  >-fs[]
QED

Theorem takeUntilIncl_cons:
  !P  l x.
      ($~ o P) h ==>
        takeUntilIncl P (h::t) = h :: takeUntilIncl P t
Proof
  rpt strip_tac
  \\ simp[takeUntilIncl_def]
  \\ CASE_TAC
  >-fs[]
QED

Theorem takeUntil_length_drop:
  !P  l x.
      EVERY ($~ o P) (TAKE x l) ==>
        LENGTH (takeUntil P l) = LENGTH (TAKE x l) + LENGTH (takeUntil P (DROP x l))
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(simp[TAKE_0, DROP_0])
  >-(Cases_on `0 < x`
    >-(simp[TAKE_cons]
    \\ `($~ o P) h` by fs[EVERY_DEF]
    \\ simp[takeUntil_length_cons]
    \\ simp[GSYM ADD_SUC]
    \\ last_assum (qspecl_then [`t`, `x - 1`] mp_tac)
      \\ disch_tac \\ fs[])
    >-fs[])
QED

Theorem takeUntilIncl_length_drop:
  !P  l x.
      EVERY ($~ o P) (TAKE x l) ==>
        LENGTH (takeUntilIncl P l) = LENGTH (TAKE x l) + LENGTH (takeUntilIncl P (DROP x l))
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(simp[TAKE_0, DROP_0])
  >-(Cases_on `0 < x`
    >-(simp[TAKE_cons]
    \\ `($~ o P) h` by fs[EVERY_DEF]
    \\ simp[takeUntilIncl_length_cons]
    \\ simp[GSYM ADD_SUC]
    \\ last_assum (qspecl_then [`t`, `x - 1`] mp_tac)
      \\ disch_tac \\ fs[])
    >-fs[])
QED

Theorem takeUntil_drop:
  !P  l x.
      EVERY ($~ o P) (TAKE x l) ==>
        takeUntil P l = TAKE x l ++ takeUntil P (DROP x l)
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(simp[TAKE_0, DROP_0])
  >-(Cases_on `0 < x`
    >-(simp[TAKE_cons]
    \\ `($~ o P) h` by fs[EVERY_DEF]
    \\ simp[takeUntil_cons]
    \\ last_assum (qspecl_then [`t`, `x - 1`] mp_tac)
      \\ disch_tac \\ fs[])
    >-(fs[]))
QED

Theorem takeUntilIncl_drop:
  !P  l x.
      EVERY ($~ o P) (TAKE x l) ==>
        takeUntilIncl P l = TAKE x l ++ takeUntilIncl P (DROP x l)
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(simp[TAKE_0, DROP_0])
  >-(Cases_on `0 < x`
    >-(simp[TAKE_cons]
    \\ `($~ o P) h` by fs[EVERY_DEF]
    \\ simp[takeUntilIncl_cons]
    \\ last_assum (qspecl_then [`t`, `x - 1`] mp_tac)
      \\ disch_tac \\ fs[])
    >-(fs[]))
QED

Theorem takeUntil_exists_in_prefix:
  !P  l x.
      EXISTS P (TAKE x l) ==>
        takeUntil P l = takeUntil P (TAKE x l)
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(simp[TAKE_0, DROP_0])
  >-(Cases_on `0 < x`
    >-(simp[TAKE_cons]
    \\ Cases_on `P h`
    >-(simp[mllistTheory.takeUntil_def])
    >-(simp[takeUntil_cons]
    \\ last_assum (qspecl_then [`t`, `x - 1`] mp_tac)
      \\ disch_tac \\ fs[]))
    >-(fs[]))
QED

Theorem takeUntilIncl_exists_in_prefix:
  !P  l x.
      EXISTS P (TAKE x l) ==>
        takeUntilIncl P l = takeUntilIncl P (TAKE x l)
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(simp[TAKE_0, DROP_0])
  >-(Cases_on `0 < x`
    >-(simp[TAKE_cons]
    \\ Cases_on `P h`
    >-(simp[takeUntilIncl_def])
    >-(simp[takeUntilIncl_cons]
    \\ last_assum (qspecl_then [`t`, `x - 1`] mp_tac)
      \\ disch_tac \\ fs[]))
    >-(fs[]))
QED

Theorem dropUntil_take_isPrefix:
  !P l x.
      dropUntil P (TAKE x l) ≼ dropUntil P l
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(simp[TAKE_0, DROP_0])
  >-(Cases_on `0 < x`
    >-(simp[TAKE_cons]
      \\ Cases_on `P h`
      >-(simp[mllistTheory.dropUntil_def, isPREFIX_TAKE])
      >-(simp[mllistTheory.dropUntil_def]))
    >-(fs[mllistTheory.dropUntil_def]))
QED

Theorem dropUntilIncl_take_isPrefix:
  !P l x.
      dropUntilIncl P (TAKE x l) ≼ dropUntilIncl P l
Proof
  simp[dropUntilIncl_def]
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(simp[TAKE_0, DROP_0])
  >-(Cases_on `0 < x`
    >-(simp[TAKE_cons]
      \\ Cases_on `P h`
      >-(simp[mllistTheory.dropUntil_def, isPREFIX_TAKE])
      >-(simp[mllistTheory.dropUntil_def]))
    >-(fs[mllistTheory.dropUntil_def]))
QED

Theorem dropUntil_length_gt_0:
  !P l x.
      EXISTS P l ==>
        0 < LENGTH (dropUntil P l)
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EXISTS_DEF])
  >-(Cases_on `P h`
    >-(simp[mllistTheory.dropUntil_def, NOT_NIL_EQ_LENGTH_NOT_0])
    >-(simp[mllistTheory.dropUntil_def]
      \\ last_assum (qspecl_then [`t`] mp_tac)
      \\ disch_tac \\ fs[]))
QED

Theorem LENGTH_dropUntil_takeUntil:
  !P l x.
      EXISTS P l ==>
        LENGTH l = LENGTH (dropUntil P l) + LENGTH (takeUntil P l)
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(simp[mllistTheory.dropUntil_def, mllistTheory.takeUntil_def])
  >-(Cases_on `P h`
    >-(simp[mllistTheory.dropUntil_def,mllistTheory.takeUntil_def])
    >-(simp[mllistTheory.dropUntil_def, mllistTheory.takeUntil_def]
      \\ fs[GSYM SUC_ADD_SYM, SUC_ONE_ADD]))
QED

Theorem LENGTH_takeUntil_takeUntilIncl:
  !P l.
      EXISTS P l ==>
        SUC (LENGTH (takeUntil P l)) = LENGTH (takeUntilIncl P l)
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EXISTS_DEF])
  >-(Cases_on `P h`
    >-(simp[takeUntilIncl_def, mllistTheory.takeUntil_def])
    >-(simp[takeUntilIncl_def, mllistTheory.takeUntil_def]
      \\ last_assum (qspecl_then [`t`] mp_tac) \\ fs[]))
QED


Theorem LENGTH_dropUntil_takeUntilIncl:
  !P l x.
      EXISTS P l ==>
        LENGTH l = LENGTH (dropUntil P l) + LENGTH (takeUntilIncl P l) - 1
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(simp[mllistTheory.dropUntil_def, takeUntilIncl_def])
  >-(Cases_on `P h`
    >-(simp[mllistTheory.dropUntil_def,takeUntilIncl_def])
    >-(simp[mllistTheory.dropUntil_def, takeUntilIncl_def]
      \\ fs[GSYM SUC_ADD_SYM, SUC_ONE_ADD, GSYM LENGTH_takeUntil_takeUntilIncl]))
QED

Theorem LENGTH_dropUntil_leq:
  !P l.
    LENGTH (dropUntil P l) <= LENGTH l
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(simp[mllistTheory.dropUntil_def])
  >-(Cases_on `P h`
    >-(simp[mllistTheory.dropUntil_def])
    >-(simp[mllistTheory.dropUntil_def]
      \\ last_assum (qspecl_then [`t`] mp_tac) \\ strip_tac
      \\ fs[EXISTS_DEF] \\ res_tac
      \\ simp[]))
QED

Theorem LENGTH_takeUntil_exists:
  !P l.
      EXISTS P l <=>
        LENGTH (takeUntil P l) < LENGTH l
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EXISTS_DEF])
  >-(Cases_on `P h`
    >-(simp[mllistTheory.takeUntil_def])
    >-(simp[mllistTheory.takeUntil_def]
      \\ last_assum (qspecl_then [`t`] mp_tac) \\ strip_tac
      \\ fs[EXISTS_DEF] \\ res_tac))
QED

Theorem takeUntil_not_exists:
  !P l.
      ~EXISTS P l <=>
        takeUntil P l = l
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EXISTS_DEF, mllistTheory.takeUntil_def])
  >-(Cases_on `P h`
    >-(simp[mllistTheory.takeUntil_def])
    >-(simp[mllistTheory.takeUntil_def]
      \\ last_assum (qspecl_then [`t`] mp_tac) \\ strip_tac
      \\ fs[EXISTS_DEF] \\ res_tac))
QED

Theorem LENGTH_takeUntilIncl_exists_geq_1:
  !P l.
      EXISTS P l ==>
        1 <= LENGTH (takeUntilIncl P l)
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EXISTS_DEF])
  >-(Cases_on `P h`
    >-(fs[takeUntilIncl_def])
    >-(fs[takeUntilIncl_def]))
QED

Theorem takeUntilIncl_not_exists:
  !P l.
      ~EXISTS P l ==>
         takeUntilIncl P l = l
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EVERY_DEF, takeUntilIncl_def])
  >-(Cases_on `P h`
    >-(fs[EVERY_DEF])
    >-(fs[takeUntilIncl_def]))
QED

Theorem dropUntilIncl_not_exists:
  !P l.
      ~EXISTS P l ==>
        dropUntilIncl P l = []
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EVERY_DEF, dropUntilIncl_def, mllistTheory.dropUntil_def])
  >-(Cases_on `P h`
    >-(fs[EVERY_DEF])
    >-(fs[dropUntilIncl_def, mllistTheory.dropUntil_def]))
QED

Theorem LENGTH_dropUntilIncl:
  !P l.
      (EXISTS P l ==>
        LENGTH (dropUntilIncl P l) < LENGTH l) /\
      (~(EXISTS P l) ==>
        LENGTH (dropUntilIncl P l) = 0) /\
      (LENGTH (dropUntilIncl P l) <= LENGTH l)
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EVERY_DEF, dropUntilIncl_def, mllistTheory.dropUntil_def])
  >-(Cases_on `P h`
    >-(fs[dropUntilIncl_def, mllistTheory.dropUntil_def])
    >-(fs[dropUntilIncl_def, mllistTheory.dropUntil_def]
      \\ last_assum (qspecl_then [`t`] mp_tac) \\ disch_tac \\ fs[]))
  >-(`~(EXISTS P [])` by metis_tac[EXISTS_NOT_EVERY]
    \\ fs[dropUntilIncl_not_exists])
  >-(`~(EXISTS P (h::t))` by metis_tac[EXISTS_NOT_EVERY]
    \\ fs[dropUntilIncl_not_exists])
  >-(fs[dropUntilIncl_def, mllistTheory.dropUntil_def])
  \\ cases_on `P h` >- fs[LENGTH,dropUntilIncl_def, mllistTheory.dropUntil_def]
  \\ fs[LENGTH,dropUntilIncl_def, mllistTheory.dropUntil_def]
  \\ last_assum (qspecl_then [`t`] mp_tac) \\ disch_tac
  \\ cases_on `EXISTS P t` >- fs[]
  \\ fs[LENGTH_dropUntil_leq]
QED

Theorem take_drop_eq_hd_cons:
  !t x y.
      y < LENGTH l ==>
        (HD (DROP y l)::TAKE x (DROP (y + 1) l)) = TAKE (x + 1) (DROP y l)
Proof
  rpt strip_tac
  \\ Cases_on `l`
  >-(fs[DROP_NIL])
  >-(simp[DROP_cons]
    \\ Cases_on `(DROP y (h::t))`
    >-(fs[DROP_NIL])
    >-(cases_on `0 < x + 1`
      >-(simp[TAKE_cons]
        \\ Cases_on `0 < y`
        >-(imp_res_tac DROP_EQ_CONS_IMP_DROP_SUC
          \\ fs[SUC_ONE_ADD]
          \\ `1 + (y - 1) = y` by decide_tac
          \\ rw[])
        >-(fs[DROP_0]))
      >-(fs[TAKE_0])))
QED

Theorem chr_neq_ord_o_w8_neq:
  a <> b ==> (n2w:num->word8 o ORD) a <> (n2w:num->word8 o ORD) b
Proof
  strip_tac
  \\ cases_on `a` \\ cases_on `b`
  \\ fs[]
QED

Theorem chr_eq_ord_o_w8_eq:
  a = b ==> (n2w:num->word8 o ORD) a = (n2w:num->word8 o ORD) b
Proof
  strip_tac
  \\ cases_on `a` \\ cases_on `b`
  \\ fs[]
QED

Theorem takeUntilIncl_length_gt_0:
  !P l x.
      EXISTS P l ==>
        0 < LENGTH (takeUntilIncl P l)
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EXISTS_DEF])
  >-(Cases_on `P h`
    >-(simp[takeUntilIncl_def, NOT_NIL_EQ_LENGTH_NOT_0])
    >-(simp[takeUntilIncl_def]
      \\ last_assum (qspecl_then [`t`] mp_tac)
      \\ disch_tac \\ fs[]))
QED

Theorem takeUntilIncl_length_leq:
  !P l.
        LENGTH (takeUntilIncl P l) <= LENGTH l
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[takeUntilIncl_def])
  >-(Cases_on `P h`
    >-(simp[takeUntilIncl_def, NOT_NIL_EQ_LENGTH_NOT_0])
    >-(simp[takeUntilIncl_def]
      \\ last_assum (qspecl_then [`t`] mp_tac)
      \\ disch_tac \\ fs[]))
QED

Theorem takeUntilIncl_exists_last:
  !P l x.
      EXISTS P l ==>
        P (LAST (takeUntilIncl P l))
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EXISTS_DEF])
  >-(Cases_on `P h`
    >-(simp[takeUntilIncl_def, NOT_NIL_EQ_LENGTH_NOT_0, LAST_DEF])
    >-(fs[takeUntilIncl_def, LAST_DEF, EXISTS_DEF]
      \\ `t <> []` by (imp_res_tac EXISTS_MEM \\ imp_res_tac NOT_NULL_MEM \\ fs[NULL_EQ])
      \\ CASE_TAC
      >-(imp_res_tac takeUntilIncl_length_gt_0 \\ rfs[NOT_NIL_EQ_LENGTH_NOT_0])
      \\ last_assum (qspecl_then [`t`] mp_tac)
      \\ disch_tac \\ fs[]))
QED


Theorem exists_chr_isSuffix:
  !P l.
      EXISTS ($= c) l ==>
        (isSuffix (str c) (implode (takeUntilIncl ($= c) l)) <=>
          ($= c) (LAST (takeUntilIncl ($= c) l)))
Proof
  strip_tac
  \\ completeInduct_on `LENGTH (l:char list)`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(rfs[EXISTS_DEF])
  >-(Cases_on `($= c) h`
    >-(simp[takeUntilIncl_def, isSuffix_def, str_def, implode_def, NOT_NIL_EQ_LENGTH_NOT_0,
              isStringThere_SEG, LAST_DEF])
    >-(simp[takeUntilIncl_def, isSuffix_def, str_def, implode_def, NOT_NIL_EQ_LENGTH_NOT_0,
              isStringThere_SEG, LAST_DEF]
      \\ fs[EXISTS_DEF]
      \\ `t <> []` by (imp_res_tac EXISTS_MEM \\ imp_res_tac NOT_NULL_MEM \\ fs[NULL_EQ])
      \\ CASE_TAC
      >-(imp_res_tac takeUntilIncl_length_gt_0 \\ rfs[NOT_NIL_EQ_LENGTH_NOT_0])
      \\ simp[GSYM isStringThere_SEG]
      \\ fs[isSuffix_def, GSYM implode_def, GSYM str_def]
      \\ imp_res_tac LENGTH_takeUntilIncl_exists_geq_1
      \\ last_assum (qspecl_then [`t`] mp_tac)
      \\ disch_tac \\ fs[] \\ res_tac \\ rfs[]
      \\ eq_tac
      >-(rfs[isStringThere_SEG, str_def, implode_def]
      \\ rfs[SEG1]
      \\ Cases_on `takeUntilIncl ($= c) t`
      >-fs[LAST_DEF]
      >-(`EL (STRLEN (STRING h' t')) (STRING h (STRING h' t')) =
        EL (STRLEN (STRING h' t') − 1) (STRING h' t')` by fs[STRLEN_THM, STRLEN_DEF]
      \\ rw[]
      \\ fs[EL, LAST_DEF]))
      >-(rfs[isStringThere_SEG, str_def, implode_def]
      \\ rfs[SEG1]
      \\ Cases_on `takeUntilIncl ($= c) t`
      >-fs[LAST_DEF]
      >-(`EL (STRLEN (STRING h' t')) (STRING h (STRING h' t')) =
        EL (STRLEN (STRING h' t') − 1) (STRING h' t')` by fs[STRLEN_THM, STRLEN_DEF]
      \\ rw[]))))
QED

Theorem not_exists_chr_not_isSuffix:
  !l.
      0 < LENGTH l /\
      ~(EXISTS ($= c) l) ==>
        ~(isSuffix (str c) (implode l))
Proof
  completeInduct_on `LENGTH (l:string)`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(rfs[isSuffix_def])
  >-(fs[takeUntilIncl_def, isSuffix_def, str_def, implode_def, NOT_NIL_EQ_LENGTH_NOT_0,
              isStringThere_SEG]
    \\ `1 + STRLEN t <= STRLEN t + 1` by decide_tac
    \\ Cases_on `0 < STRLEN t`
    >-(fs[SEG_CONS]
      \\ last_assum (qspecl_then [`t`] mp_tac)
      \\ disch_tac \\ fs[]
      >-(fs[])
      >-(fs[GSYM NOT_F]))
    >-(fs[] \\ fs[SEG1]))
QED

Theorem isSuffix_char_strlen_gt_0:
  !P l.
        isSuffix (str c) (implode l) ==> 0 < STRLEN l
Proof
  strip_tac
  \\ completeInduct_on `LENGTH (l:string)`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[isSuffix_def, implode_def, str_def])
  >-(Cases_on `($= c) h`
    >-(simp[takeUntilIncl_def, isSuffix_def, str_def, implode_def, NOT_NIL_EQ_LENGTH_NOT_0,
              isStringThere_SEG])
    >-(simp[takeUntilIncl_def, isSuffix_def, str_def, implode_def, NOT_NIL_EQ_LENGTH_NOT_0,
              isStringThere_SEG]))
QED

Theorem STRCAT_eq_MAP_n2w_o_ORD_append:
  STRCAT l r = MAP (CHR o w2n:word8->num) (MAP (n2w o ORD) l ++ MAP (n2w o ORD) r)
Proof
  fs[STRCAT_EQNS, MAP_MAP_o, CHR_w2n_n2w_ORD]
QED

Theorem EL_STRCAT:
  !l.
        EL (STRLEN r - 1) r = EL (STRLEN r - 1 + STRLEN l) (STRCAT l r)
Proof
  fs[EL_APPEND_EQN,MAP_MAP_o, CHR_w2n_n2w_ORD]
QED

Theorem isSuffix_char_implode_strcat:
  !l r c.
        0 < STRLEN r ==>
          (isSuffix (str c) (implode r) <=> isSuffix (str c) (implode (STRCAT l r)))
Proof
  rpt strip_tac
  \\ fs[isSuffix_def, implode_def, str_def, SUC_ONE_ADD, isStringThere_SEG, SEG1]
  \\ eq_tac
  >-(strip_tac
    \\ fs[EL_APPEND_EQN,MAP_MAP_o, CHR_w2n_n2w_ORD]
    \\ CASE_TAC
    >-(fs[NOT_NIL_EQ_LENGTH_NOT_0]))
  >-(strip_tac
    \\ fs[EL_APPEND_EQN,MAP_MAP_o, CHR_w2n_n2w_ORD]
    \\ CASE_TAC
    >-(fs[NOT_NIL_EQ_LENGTH_NOT_0]))
QED

Theorem exists_eq_o_map:
  !P l.
      EXISTS ($= ((n2w ∘ ORD) x)) l <=>
        EXISTS ($= x) (MAP (CHR o w2n) (l:word8 list))
Proof
  strip_tac
  \\ completeInduct_on `LENGTH (l:word8 list)`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EXISTS_DEF])
  >-(Cases_on `($= ((n2w:num->word8 ∘ ORD) x)) h`
    >-(fs[EXISTS_DEF]
      \\ disj1_tac
      \\ metis_tac[CHR_w2n_n2w_ORD_simp, o_THM])
    >-(fs[EXISTS_DEF]
      \\ eq_tac
      >-(strip_tac
        \\ disj2_tac \\ fs[])
      >-(strip_tac
        \\ imp_res_tac chr_eq_ord_o_w8_eq
        \\ fs[o_THM])))
QED

Theorem exists_eq_o_map2:
    !P l.
      EXISTS ($= ((n2w ∘ ORD) x)) (MAP (n2w:num->word8 o ORD) l) <=>
        EXISTS ($= x) (l:string)
Proof
  strip_tac
  \\ completeInduct_on `LENGTH (l:string)`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EXISTS_DEF])
  >-(Cases_on `($= x) h`
    >-(fs[EXISTS_DEF]
      \\ disj1_tac
      \\ metis_tac[CHR_w2n_n2w_ORD_simp, o_THM])
    >-(fs[EXISTS_DEF]
      \\ eq_tac
      >-(strip_tac
        \\ Cases_on `x` \\ Cases_on `h` \\ fs[])
      >-(strip_tac
        \\ disj2_tac \\ fs[])))
QED

Theorem map_w82c_takeUntilIncl_eq_takeUntilIncl_map_c2w8:
  !P l.
      takeUntilIncl ($= c) (MAP (CHR ∘ w2n) (l:word8 list)) =
        MAP (CHR o w2n:word8->num) (takeUntilIncl ($= ((n2w:num->word8 o ORD) c)) (l:word8 list))
Proof
  strip_tac
  \\ completeInduct_on `LENGTH (l:word8 list)`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[takeUntilIncl_def])
  >-(Cases_on `c = CHR (w2n (h:word8))`
    >-(fs[takeUntilIncl_def])
    >-(fs[takeUntilIncl_def]
      \\ imp_res_tac chr_neq_ord_o_w8_neq
      \\ fs[o_THM]))
QED

Theorem map_w82c_takeUntilIncl_eq_takeUntilIncl_map_c2w8_2:
  !P l.
      takeUntilIncl ($= c) (l:string) =
        MAP (CHR o w2n:word8->num)
          (takeUntilIncl ($= ((n2w:num->word8 o ORD) c)) (MAP (n2w:num->word8 o ORD) l))
Proof
  strip_tac
  \\ completeInduct_on `LENGTH (l:string)`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[takeUntilIncl_def])
  >-(Cases_on `c = h`
    >-(fs[takeUntilIncl_def])
    >-(fs[takeUntilIncl_def]
      \\ imp_res_tac chr_neq_ord_o_w8_neq
      \\ fs[o_THM]))
QED

Theorem map_w82c_dropUntilIncl_eq_dropUntilIncl_map_c2w8:
  !P l.
      dropUntilIncl ($= c) (MAP (CHR ∘ w2n) (l:word8 list)) =
        MAP (CHR o w2n:word8->num) (dropUntilIncl ($= ((n2w:num->word8 o ORD) c)) (l:word8 list))
Proof
  strip_tac
  \\ completeInduct_on `LENGTH (l:word8 list)`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[dropUntilIncl_def, mllistTheory.dropUntil_def])
  >-(Cases_on `c = CHR (w2n (h:word8))`
    >-(fs[dropUntilIncl_def, mllistTheory.dropUntil_def])
    >-(fs[dropUntilIncl_def, mllistTheory.dropUntil_def]
      \\ imp_res_tac chr_neq_ord_o_w8_neq
      \\ fs[o_THM]))
QED

Theorem map_w82c_dropUntilIncl_eq_dropUntilIncl_map_c2w8_2:
  !P l.
      dropUntilIncl ($= c) (l:string) =
        MAP (CHR o w2n:word8->num)
          (dropUntilIncl ($= ((n2w:num->word8 o ORD) c)) (MAP (n2w:num->word8 o ORD) l))
Proof
  strip_tac
  \\ completeInduct_on `LENGTH (l:string)`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[dropUntilIncl_def, mllistTheory.dropUntil_def])
  >-(Cases_on `c = h`
    >-(fs[dropUntilIncl_def, mllistTheory.dropUntil_def]
      \\ fs[MAP_MAP_o, CHR_w2n_n2w_ORD])
    >-(fs[dropUntilIncl_def, mllistTheory.dropUntil_def]
      \\ imp_res_tac chr_neq_ord_o_w8_neq
      \\ fs[o_THM]))
QED

Theorem takeUntilIncl_exists:
  !P l x.
      EXISTS P l ==>
        EXISTS P (takeUntilIncl P l)
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EXISTS_DEF])
  >-(Cases_on `P h`
    >-(simp[takeUntilIncl_def, NOT_NIL_EQ_LENGTH_NOT_0])
    >-(fs[takeUntilIncl_def, EXISTS_DEF]))
QED

Theorem takeUntilIncl_append_exists_l:
  !P l x.
      EXISTS P l ==>
        takeUntilIncl P (l ++ r) = takeUntilIncl P l
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EXISTS_DEF])
  >-(simp[APPEND_EQ_CONS]
    \\ Cases_on `P h`
    >-(simp[takeUntilIncl_def, NOT_NIL_EQ_LENGTH_NOT_0])
    >-(fs[takeUntilIncl_def, EXISTS_DEF]))
QED

Theorem takeUntil_append_exists_l:
  !P l x.
      EXISTS P l ==>
        takeUntil P (l ++ r) = takeUntil P l
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EXISTS_DEF])
  >-(simp[APPEND_EQ_CONS]
    \\ Cases_on `P h`
    >-(simp[mllistTheory.takeUntil_def, NOT_NIL_EQ_LENGTH_NOT_0])
    >-(simp[mllistTheory.takeUntil_def, EXISTS_DEF]
      \\ last_assum (qspecl_then [`t`] mp_tac)
      \\ disch_tac \\ fs[]))
QED

Theorem takeUntil_append_not_exists_l:
  !P l x.
      ~(EXISTS P l)  ==>
        takeUntil P (l ++ r) = l ++ takeUntil P r
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EXISTS_DEF])
  >-(Cases_on `P h` >- fs[EVERY_DEF]
    >-(simp[mllistTheory.takeUntil_def]
      \\ last_assum (qspecl_then [`t`] mp_tac)
      \\ disch_tac \\ fs[]))
QED

Theorem takeUntilIncl_append_not_exists_l:
  !P l x.
      ~(EXISTS P l) ==>
        takeUntilIncl P (l ++ r) = l ++ takeUntilIncl P r
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EXISTS_DEF])
  >-(Cases_on `P h` >- fs[EVERY_DEF]
    >-(simp[takeUntilIncl_def]
      \\ last_assum (qspecl_then [`t`] mp_tac)
      \\ disch_tac \\ fs[]))
QED

Theorem dropUntilIncl_append_exists_l:
  !P l x.
      EXISTS P l ==>
        dropUntilIncl P (l ++ r) = dropUntilIncl P l ++ r
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EXISTS_DEF])
  >-(Cases_on `P h` >- fs[mllistTheory.dropUntil_def, dropUntilIncl_def]
    >-(fs[dropUntilIncl_def, mllistTheory.dropUntil_def]))
QED

Theorem dropUntilIncl_append_not_exists_l:
  !P l x.
      ~(EXISTS P l)  ==>
        dropUntilIncl P (l ++ r) = dropUntilIncl P r
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EXISTS_DEF])
  >-(Cases_on `P h` >- fs[mllistTheory.dropUntil_def, dropUntilIncl_def]
    >-(fs[dropUntilIncl_def, mllistTheory.dropUntil_def]))
QED

Theorem LENGTH_dropUntil_takeUntilIncl2:
  !P l x.
      EXISTS P l ==>
        SUC (LENGTH l) = LENGTH (dropUntil P l) + LENGTH (takeUntilIncl P l)
Proof
  strip_tac
  \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[EVERY_DEF])
  >-(Cases_on `P h`
    >-(simp[mllistTheory.dropUntil_def,takeUntilIncl_def])
    >-(simp[mllistTheory.dropUntil_def, takeUntilIncl_def]
      \\ fs[GSYM SUC_ADD_SYM, SUC_ONE_ADD, GSYM LENGTH_takeUntil_takeUntilIncl]))
QED

Theorem LENGTH_dropUntilIncl_takeUntilIncl:
  !P l.
    LENGTH l = LENGTH (dropUntilIncl P l) + LENGTH (takeUntilIncl P l)
Proof
  `!P l.
      EXISTS P l ==>
        LENGTH l = LENGTH (dropUntilIncl P l) + LENGTH (takeUntilIncl P l)`
        by
          (strip_tac
          \\ completeInduct_on `LENGTH l`
          \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
          \\ Cases_on `l`
          >-(simp[mllistTheory.dropUntil_def, dropUntilIncl_def, takeUntilIncl_def])
          >-(Cases_on `P h`
            >-(simp[mllistTheory.dropUntil_def,dropUntilIncl_def,takeUntilIncl_def])
            >-(simp[mllistTheory.dropUntil_def, dropUntilIncl_def, takeUntilIncl_def]
              \\ fs[GSYM SUC_ADD_SYM, SUC_ONE_ADD, GSYM LENGTH_takeUntil_takeUntilIncl]
              \\ fs[dropUntilIncl_def])))
  \\ rpt strip_tac \\ reverse (cases_on `EXISTS P l`)
  >-(fs[dropUntilIncl_not_exists, takeUntilIncl_not_exists])
  \\ last_assum (qspecl_then [`P`,`l`] mp_tac) \\ strip_tac \\ fs[]
QED

Theorem LENGTH_dropUntilIncl_dropUntil:
  !P ls.
      LENGTH (dropUntilIncl P ls) = LENGTH (dropUntil P ls) - 1
Proof
  strip_tac \\ completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[dropUntilIncl_def, mllistTheory.dropUntil_def]
  \\ cases_on `P h`
  >- fs[dropUntilIncl_def, mllistTheory.dropUntil_def]
  >- fs[dropUntilIncl_def, mllistTheory.dropUntil_def]
QED

Definition lineForwardFD_def:
    lineForwardFD buff fs fd extra =
         case get_file_content fs fd of
           NONE => fs
         | SOME (content,pos') =>
           if EXISTS ($= (10w:word8)) buff then fs
            else if pos' < STRLEN content then
             (let
                (l,r) = SPLITP ($= #"\n") (DROP pos' content)
              in
                forwardFD fs fd (LENGTH extra + STRLEN l + if NULL r then 0 else 1))
           else fs
End

Definition takeLine_def:
  takeLine s = takeUntilIncl ($= #"\n") s
End

Definition dropLine_def:
  dropLine s = dropUntilIncl ($= #"\n") s
End

Definition inputLine_def:
  inputLine s =
    implode (if EXISTS ($= #"\n") s
             then takeLine s
             else STRCAT s "\n")
End

Definition gen_inputLine_def:
  gen_inputLine c s =
    implode (if EXISTS ($= c) s
             then takeUntilIncl ($= c) s
             else STRCAT s [c])
End

Theorem SPLITP_takeUntil_dropUntil:
  !P ls.
    SPLITP P ls = (takeUntil P ls, dropUntil P ls)
Proof
  strip_tac \\ completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `ls` >- fs[SPLITP, mllistTheory.takeUntil_def, mllistTheory.dropUntil_def]
  \\ Cases_on `P h` >- fs[SPLITP, mllistTheory.takeUntil_def, mllistTheory.dropUntil_def]
  \\ fs[SPLITP, mllistTheory.takeUntil_def, mllistTheory.dropUntil_def]
QED

Theorem LENGTH_dropUntil:
  !P ls.
    (EXISTS P ls ==> 0 < LENGTH (dropUntil P ls)) /\
    (~EXISTS P ls ==> LENGTH (dropUntil P ls) = 0) /\
    LENGTH (dropUntil P ls) <= LENGTH ls
Proof
  rpt strip_tac
  >- fs[dropUntil_length_gt_0]
  >- (Induct_on `ls` >- fs[mllistTheory.dropUntil_def]
     \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
     \\ cases_on `P h` >- fs[] >-fs[mllistTheory.dropUntil_def])
  \\ fs[LENGTH_dropUntil_leq]
QED

Theorem LENGTH_takeUntilIncl_w8_takeUntilIncl_chr:
  !ls.
    LENGTH (takeUntilIncl ($= (10w:word8)) (MAP (n2w ∘ ORD) (DROP pos content))) =
      LENGTH (takeUntilIncl ($= #"\n") (DROP pos content))
Proof
  rpt strip_tac
  \\ `(10w:word8) = (n2w o ORD) #"\n"` by fs[]
  \\ fs[map_w82c_takeUntilIncl_eq_takeUntilIncl_map_c2w8_2]
QED

Theorem takeLine_hd_not_newline:
  !h t.
      h <> #"\n" ==>
        takeLine (STRING h t) = h :: takeLine t
Proof
  fs[takeLine_def, takeUntilIncl_def]
QED

Theorem takeLine_hd_newline:
  !h t.
      h = #"\n" ==>
        takeLine (STRING h t) = STRING #"\n" ""
Proof
  fs[takeLine_def, takeUntilIncl_def]
QED

Theorem FIELDS_hd_newline:
  !t.
        FIELDS ($= #"\n") (STRING #"\n" t) = "":: FIELDS ($= #"\n") t
Proof
  rpt strip_tac
  \\ fs[FIELDS_def, SPLITP]
QED

Theorem SPLITP_takeUntil:
  !l.
        SPLITP ($= #"\n") l =
          (takeUntil ($= #"\n") l, DROP (LENGTH (takeUntil ($= #"\n") l)) l)
Proof
  completeInduct_on `LENGTH (l:string)`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[SPLITP, mllistTheory.takeUntil_def])
  >-(Cases_on `h = #"\n"`
    >-fs[SPLITP, mllistTheory.takeUntil_def]
    >-(fs[SPLITP, mllistTheory.takeUntil_def]))
QED

Theorem LENGTH_takeUntil:
  !P l.
      LENGTH (takeUntil P l) <= LENGTH l
Proof
  strip_tac \\ completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-fs[mllistTheory.takeUntil_def]
  >-(fs[mllistTheory.takeUntil_def]
    \\ CASE_TAC >- fs[]
    \\ fs[LENGTH])
QED

Theorem FIELDS_takeUntil:
  !l.
      LENGTH (takeUntil ($= #"\n") l) < LENGTH l ==>
      FIELDS ($= #"\n") l =
          takeUntil ($= #"\n") l ::
            FIELDS ($= #"\n") (TL (DROP (LENGTH (takeUntil ($= #"\n") l)) l))
Proof
  completeInduct_on `LENGTH (l:string)`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[mllistTheory.takeUntil_def])
  >-(Cases_on `h = #"\n"`
    >-(simp[mllistTheory.takeUntil_def]
      \\ fs[FIELDS_hd_newline])
    >-(fs[FIELDS_def, SPLITP_takeUntil]
      \\ `~(NULL (takeUntil ($= #"\n") (STRING h t)))` by fs[mllistTheory.takeUntil_def, NULL_DEF]
      \\ simp[] \\ Cases_on `LENGTH (takeUntil ($= #"\n") (STRING h t)) = LENGTH (STRING h t)`
      >-(fs[DROP_LENGTH_TOO_LONG])
      \\ `STRLEN (takeUntil ($= #"\n") (STRING h t)) < STRLEN (STRING h t)` by fs[LENGTH_CONS]
      \\ `(DROP (STRLEN (takeUntil ($= #"\n") (STRING h t))) (STRING h t)) <> []` by fs[DROP_NIL]
      \\ Cases_on `DROP (STRLEN (takeUntil ($= #"\n") (STRING h t))) (STRING h t)`
      >- fs[]
      \\ `~(NULL (STRING h' t'))` by fs[NULL_DEF]
      \\ simp[]))
QED

Theorem splitlines_hd_newline:
  !t.
        splitlines (STRING #"\n" t) = "" :: splitlines t
Proof
  rpt strip_tac \\ fs[splitlines_def]
  \\ CASE_TAC
  >-(CASE_TAC
    >-(fs[FRONT_DEF, FIELDS_hd_newline])
    >-(fs[NULL_DEF,LAST_DEF, FIELDS_hd_newline]))
  >-(CASE_TAC
    >-(fs[NULL_DEF, LAST_DEF, FIELDS_hd_newline])
    >-(fs[FIELDS_hd_newline]))
QED

Theorem splitlines_takeUntil_exists:
  !l.
        EXISTS ($= #"\n") l ==>
        splitlines l =
          (takeUntil ($= #"\n") l ::
            splitlines (TL (DROP (LENGTH (takeUntil ($= #"\n") l)) l)))
Proof
  rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ `LENGTH (takeUntil ($= #"\n") l) < LENGTH l` by fs[LENGTH_takeUntil_exists]
  \\ Cases_on `l`
  >-(fs[splitlines_eq_nil, mllistTheory.takeUntil_def])
  >-(Cases_on `h = #"\n"`
    >-(fs[mllistTheory.takeUntil_def, splitlines_hd_newline])
    >-(simp[mllistTheory.takeUntil_def, splitlines_def]
      \\ `~(NULL (takeUntil ($= #"\n") (STRING h t)))` by fs[mllistTheory.takeUntil_def, NULL_DEF]
      \\ CASE_TAC
      >-(CASE_TAC
        >-(fs[FIELDS_takeUntil, FRONT_DEF, FIELDS_NEQ_NIL, mllistTheory.takeUntil_def])
        >-(`LENGTH (takeUntil ($= #"\n") (STRING h t)) < LENGTH (STRING h t)` by fs[LENGTH_takeUntil_exists]
          \\ cases_on `#"\n" = h` >- fs[]
          \\ ` FIELDS ($= #"\n") (STRING h t) =
                takeUntil ($= #"\n") (STRING h t)::
             FIELDS ($= #"\n")
               (TL (DROP (STRLEN (takeUntil ($= #"\n") (STRING h t))) (STRING h t)))` by fs[FIELDS_takeUntil]
          \\ fs[mllistTheory.takeUntil_def, LAST_DEF]))
      >-(cases_on `#"\n" = h` >- fs[]
        \\ `FIELDS ($= #"\n") (STRING h t) =
                takeUntil ($= #"\n") (STRING h t)::
             FIELDS ($= #"\n")
               (TL (DROP (STRLEN (takeUntil ($= #"\n") (STRING h t))) (STRING h t)))` by fs[FIELDS_takeUntil]
        \\ fs[FIELDS_takeUntil, mllistTheory.takeUntil_def] \\ rfs[]
        \\ fs[LAST_DEF])))
QED

Theorem splitlines_takeUntil_exists2:
  !l.
        EXISTS ($= #"\n") l ==>
        splitlines l =
          (takeUntil ($= #"\n") l ::
            splitlines (DROP (SUC (LENGTH (takeUntil ($= #"\n") l))) l))
Proof
  rpt strip_tac
  \\ imp_res_tac splitlines_takeUntil_exists
  \\ `DROP (SUC (STRLEN (takeUntil ($= #"\n") l))) l =
      DROP 1 (DROP (STRLEN (takeUntil ($= #"\n") l)) l)` by fs[SUC_ONE_ADD, DROP_DROP_T]
  \\ rw[] \\ cases_on `DROP (STRLEN (takeUntil ($= #"\n") l)) l`
  >-fs[takeUntilIncl_length_gt_0] >-fs[TL, DROP]
QED

Theorem splitlines_not_exists:
  !l.
        ~EXISTS ($= #"\n") l /\
        ~NULL l ==>
        splitlines l = [l]
Proof
  rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l` >- fs[splitlines_eq_nil]
  \\ `h <> #"\n"` by fs[EVERY_DEF]
  \\ fs[splitlines_def, FRONT_DEF, FIELDS_def, SPLITP, NULL_DEF]
  \\ CASE_TAC
  >-(CASE_TAC
    >-(fs[FRONT_DEF])
    >-(`SPLITP ($= #"\n") t = (t, [])`  by metis_tac[NOT_DEF,SPLITP_EVERY]
      \\ fs[FST]))
  >-(CASE_TAC
    >-(fs[FRONT_DEF]
      \\ `SPLITP ($= #"\n") t = (t, [])`  by metis_tac[NOT_DEF,SPLITP_EVERY]
      \\ fs[FST])
    >-(`SPLITP ($= #"\n") t = (t, [])`  by metis_tac[NOT_DEF,SPLITP_EVERY]
      \\ fs[FST]))
QED

Theorem TL_APPEND:
  !l r.
       0 < LENGTH l ==>
       TL (l ++ r) = (TL l ++ r)
Proof
  rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l` >- fs[]
  >-fs[TL]
QED

Theorem splitlines_append_exists_l:
  !l.
      EXISTS ($= #"\n") (l:string) ==>
        splitlines (l ++ r) =
          (takeUntil ($= #"\n") l ::
            splitlines (TL (DROP (LENGTH (takeUntil ($= #"\n") l)) l) ++ r))
Proof
  completeInduct_on `LENGTH (splitlines:string->string list (l ++ r))`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[splitlines_eq_nil, mllistTheory.takeUntil_def])
  >-(Cases_on `h = #"\n"`
    >-(fs[takeLine_def, mllistTheory.takeUntil_def, splitlines_hd_newline])
    >-(`EXISTS ($= #"\n") (STRCAT (STRING h t) r)` by fs[EXISTS_APPEND]
      \\ fs[splitlines_takeUntil_exists] >-fs[]
      \\ fs[mllistTheory.takeUntil_def]
      \\ last_assum (qspecl_then [`t`, `r`] mp_tac)
      \\ disch_tac
      \\ `takeUntil ($= #"\n") (STRCAT t r) = takeUntil ($= #"\n") t`
          by fs[takeUntil_append_exists_l] \\ rw[]
      >-(rfs[] \\ `LENGTH (takeUntil ($= #"\n") t) < LENGTH t`
                    by fs[LENGTH_APPEND,LENGTH_takeUntil_exists]
      \\ `LENGTH (takeUntil ($= #"\n") t) < LENGTH (STRCAT t r)`
                    by fs[LENGTH_APPEND,LENGTH_takeUntil_exists]
      \\ fs[DROP_APPEND1] \\ fs[TL_APPEND])
      >-(`takeUntil ($= #"\n") (STRCAT t r) = takeUntil ($= #"\n") t`
          by fs[takeUntil_append_exists_l]
        \\ `LENGTH (takeUntil ($= #"\n") t) < LENGTH t`
                    by fs[LENGTH_APPEND,LENGTH_takeUntil_exists]
        \\ `LENGTH (takeUntil ($= #"\n") t) < LENGTH (STRCAT t r)`
                    by fs[LENGTH_APPEND,LENGTH_takeUntil_exists]
        \\ fs[DROP_APPEND1] \\ fs[TL_APPEND]
        \\ `EXISTS ($= #"\n") (STRCAT (TL (DROP (STRLEN (takeUntil ($= #"\n") t)) t)) r)`
            by fs[EXISTS_APPEND] \\ fs[splitlines_takeUntil_exists])))
QED

Theorem splitlines_append_exists_r:
  !l.
      ~(EXISTS ($= #"\n") (l:string)) /\
      EXISTS ($= #"\n") (r:string) ==>
        splitlines (l ++ r) =
          ((l ++ (takeUntil ($= #"\n") r)) ::
            splitlines (TL (DROP (LENGTH (takeUntil ($= #"\n") r)) r)))
Proof
  completeInduct_on `LENGTH (splitlines:string->string list (l ++ r))`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `r`
  >-(`LENGTH (takeUntil ($= #"\n") r) < LENGTH r` by fs[LENGTH_takeUntil_exists]
    \\ fs[splitlines_takeUntil_exists])
  >-(`EXISTS ($= #"\n") (STRCAT l (STRING h t))` by fs[EXISTS_APPEND]
    \\ `splitlines (STRCAT l (STRING h t)) =
         takeUntil ($= #"\n") (STRCAT l (STRING h t))::
             splitlines (TL (DROP (STRLEN (takeUntil ($= #"\n") (STRCAT l (STRING h t)))) (STRCAT l (STRING h t))))`
          by fs[splitlines_takeUntil_exists]
    \\ imp_res_tac NOT_EXISTS \\ imp_res_tac takeUntilIncl_append_not_exists_l
    \\ `takeUntil ($= #"\n") (l ++ (STRING h t)) = l ++ (takeUntil ($= #"\n") (STRING h t))`
        by metis_tac[takeUntil_append_not_exists_l] \\ rw[]
    \\ rfs[splitlines_takeUntil_exists]
    >-(simp[mllistTheory.takeUntil_def, DROP_APPEND1, DROP_LENGTH_TOO_LONG])
    >-(simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]
      \\ Cases_on `h = #"\n"` >-(simp[mllistTheory.takeUntil_def])
      \\ simp[mllistTheory.takeUntil_def]))
QED

Theorem splitlines_not_exists2:
  !l.
        ~(EXISTS ($= #"\n") l) ==>
        splitlines l = if l = "" then [] else [l]
Proof
  rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l` >- fs[]
  \\ `h <> #"\n"` by fs[EVERY_DEF]
  \\ fs[splitlines_def, FRONT_DEF, FIELDS_def, SPLITP, NULL_DEF]
  \\ CASE_TAC
  >-(CASE_TAC
    >-(fs[FRONT_DEF])
    >-(`SPLITP ($= #"\n") t = (t, [])`  by metis_tac[NOT_DEF,SPLITP_EVERY]
      \\ fs[FST]))
  >-(CASE_TAC
    >-(fs[FRONT_DEF]
      \\ `SPLITP ($= #"\n") t = (t, [])`  by metis_tac[NOT_DEF,SPLITP_EVERY]
      \\ fs[FST])
    >-(`SPLITP ($= #"\n") t = (t, [])`  by metis_tac[NOT_DEF,SPLITP_EVERY]
      \\ fs[FST]))
QED

Theorem splitlines_append_not_exists_l:
  !l.
      ~(EXISTS ($= #"\n") (l:string)) /\ ~NULL (l ++ r) ==>
        splitlines (l ++ r) =
          ((l ++ (takeUntil ($= #"\n") r)) ::
            splitlines (DROP (SUC (LENGTH (takeUntil ($= #"\n") r))) r))
Proof
  rpt strip_tac
  \\ Cases_on `EXISTS ($= #"\n") r`
  >-(imp_res_tac splitlines_append_exists_r
    \\ `DROP (SUC (STRLEN (takeUntil ($= #"\n") r))) r =
      DROP 1 (DROP (STRLEN (takeUntil ($= #"\n") r)) r)` by fs[SUC_ONE_ADD, DROP_DROP_T]
    \\ rw[] \\ cases_on `DROP (STRLEN (takeUntil ($= #"\n") r)) r`
    >-(fs[SUC_ONE_ADD] \\ `r <> ""` by fs[EXISTS_DEF])
    \\ fs[TL, DROP])
  \\ `~EXISTS ($= #"\n") (STRCAT l r)` by fs[EXISTS_APPEND]
  \\ `~NULL (l ++ r)` by fs[] \\ fs[splitlines_not_exists]
  \\ `~EXISTS ($= #"\n") r` by metis_tac[EXISTS_NOT_EVERY]
  \\ fs[takeUntil_not_exists, DROP_LENGTH_TOO_LONG]
QED

Theorem LENGTH_splitlines:
  !ls. (NULL (LAST (FIELDS ($= #"\n") ls)) ==>
    LENGTH (splitlines ls) = STRLEN (FILTER ($= #"\n") ls)) /\
     (~(NULL (LAST (FIELDS ($= #"\n") ls))) ==>
    LENGTH (splitlines ls) = STRLEN (FILTER ($= #"\n") ls) + 1)
Proof
  strip_tac
  \\ conj_tac
  >-(strip_tac \\ simp[splitlines_def, LENGTH_FIELDS, LENGTH_FRONT])
  >-(strip_tac \\ simp[splitlines_def, LENGTH_FIELDS])
QED

Theorem FILTER_dropUntilIncl:
  !ls. (EXISTS P ls ==> FILTER P (dropUntilIncl P ls) = TL (FILTER P ls)) /\
        (~(EXISTS P ls) ==> FILTER P (dropUntilIncl P ls) = [])
Proof
  strip_tac
  \\ completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  >-(cases_on `ls` >- fs[EXISTS_DEF]
    \\ Cases_on `P h` >-(fs[FILTER, dropUntilIncl_def, mllistTheory.dropUntil_def])
    \\ fs[FILTER, dropUntilIncl_def, mllistTheory.dropUntil_def]
    \\ fs[GSYM dropUntilIncl_def])
  >-(cases_on `ls` >- fs[dropUntilIncl_def, mllistTheory.dropUntil_def]
    \\ Cases_on `P h` >-(fs[FILTER, dropUntilIncl_def, mllistTheory.dropUntil_def])
    \\ fs[FILTER, dropUntilIncl_def, mllistTheory.dropUntil_def])
QED

Theorem isPREFIX_FILTER:
  !ls bs. ls ≼ bs ==> FILTER P ls ≼ FILTER P bs
Proof
  strip_tac
  \\ completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[FILTER, isPREFIX]
  \\ cases_on `bs` >- fs[isPREFIX]
  \\ `h = h'` by fs[isPREFIX]
  \\ cases_on `P h`
  >-(`P h'` by metis_tac[] \\ fs[FILTER])
  >-(`~(P h')` by metis_tac[] \\ fs[FILTER])
QED

Theorem LENGTH_FILTER_EXISTS:
  !ls.
    (EXISTS P ls ==> 0 < LENGTH (FILTER P ls)) /\
    (~(EXISTS P ls) ==> LENGTH (FILTER P ls) = 0)
Proof
  strip_tac
  \\ conj_tac
  >-(completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[EXISTS_DEF]
  \\ cases_on `P h`>- fs[FILTER]
  \\ fs[FILTER])
  >-(completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[EXISTS_DEF]
  \\ cases_on `P h`>- fs[FILTER]
  \\ fs[FILTER])
QED

Theorem LENGTH_isPREFIX:
  !ls bs. ls ≼ bs ==> LENGTH ls <= LENGTH bs
Proof
  strip_tac
  \\ completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[]
  \\ cases_on `bs` >- fs[isPREFIX]
  \\ simp[LENGTH]
  \\ last_assum (qspecl_then [`t`, `t'`] mp_tac) \\ disch_tac
  \\ fs[isPREFIX]
QED

Theorem isPREFIX_dropUntilIncl_LENGTH_FILTER:
  !ls bs.
    ls ≼ dropUntilIncl P bs ==>
    (EXISTS P bs ==>
    LENGTH (FILTER P ls) < LENGTH (FILTER P bs)) /\
    (~(EXISTS P bs) ==>
      LENGTH (FILTER P ls) = 0)
Proof
  strip_tac
  \\ completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ imp_res_tac isPREFIX_FILTER
  \\ pop_assum (qspecl_then [`P`] mp_tac) \\ disch_tac
  \\ fs[FILTER_APPEND, FILTER_dropUntilIncl]
  \\ cases_on `ls`
  >-(`LENGTH (FILTER P []) = 0` by fs[FILTER]
    \\ `0 < LENGTH (FILTER P bs)` by  fs[LENGTH_FILTER_EXISTS]
    \\ fs[])
  >-(imp_res_tac FILTER_dropUntilIncl
  \\ `LENGTH (FILTER P (h::t)) <= LENGTH (TL (FILTER P bs))` by fs[LENGTH_isPREFIX]
  \\ `FILTER P (h::t) ≼ (TL (FILTER P bs))` by fs[]
  \\ imp_res_tac LENGTH_FILTER_EXISTS
  \\ fs[LENGTH_TL])
  >-(fs[FILTER])
  >-(`~(EXISTS P bs)` by metis_tac[EXISTS_NOT_EVERY]
    \\ fs[FILTER_dropUntilIncl])
QED

Theorem isPREFIX_EQ_LENGTH:
  !ls rs.
    (LENGTH ls = LENGTH rs  /\ ls ≼ rs) <=>
      ls = rs
Proof
    completeInduct_on `LENGTH ls`
    \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
    \\ eq_tac
    >-(cases_on `ls` >- fs[] \\ cases_on `rs` >-fs[]
      \\ fs[isPREFIX_THM] \\ last_assum (qspecl_then [`t`,`t'`] mp_tac)
      \\ disch_tac \\ fs[] \\ rpt strip_tac \\ res_tac)
    >-(cases_on `ls` >- fs[] \\ cases_on `rs` >-fs[]
      \\ fs[isPREFIX_THM] \\ last_assum (qspecl_then [`t`,`t'`] mp_tac))
QED

Theorem NULL_LAST_FIELDS_IMPL_P_LAST:
  !ls.
    ls <> [] ==> (NULL (LAST (FIELDS P ls)) ==> P (LAST ls))
Proof
  completeInduct_on `LENGTH (ls:string)`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `FIELDS P ls` >- fs[FIELDS_NEQ_NIL]
  \\ cases_on `STRLEN h < STRLEN ls`
  >-(imp_res_tac FIELDS_next \\ fs[] \\ cases_on `SUC (STRLEN h) < LENGTH ls`
    >-(`LAST (DROP (SUC (STRLEN h)) ls) = LAST ls` by metis_tac[last_drop]
      \\ rveq \\ `FIELDS P (DROP (SUC (STRLEN h)) ls) <> []` by fs[FIELDS_NEQ_NIL]
      \\ fs[LAST_DEF] \\ last_assum (qspecl_then [`DROP (SUC (STRLEN h)) ls`] mp_tac)
      \\ disch_tac \\ fs[LENGTH_DROP, DROP_NIL]
      \\ reverse (cases_on `0 < STRLEN ls`) >- fs[LENGTH_NIL]
      \\ fs[] \\ `~(SUC (STRLEN h) >= STRLEN ls)` by decide_tac
      \\ fs[] \\ `FIELDS P (DROP (SUC (STRLEN h)) ls) <> []` by fs[FIELDS_NEQ_NIL]
      \\ fs[LAST_DEF] \\ res_tac \\ `P (LAST (DROP (SUC (STRLEN h)) ls)) = P (LAST ls)` by metis_tac[]
      \\ fs[])
    >-(fs[DROP_LENGTH_TOO_LONG, FIELDS_def] \\ rveq \\ fs[LAST_DEF]
      \\ imp_res_tac LESS_SUC_NOT \\ imp_res_tac NOT_LESS
      \\ `STRLEN h + 1 = STRLEN ls` by (fs[SUC_ONE_ADD] \\ decide_tac)
      \\ `LENGTH (STRCAT h (STRING c "")) = STRLEN h + STRLEN (STRING c "")` by fs[LENGTH_APPEND]
      \\ `STRLEN (STRING c "") = 1` by fs[STRLEN_DEF]
      \\ `LENGTH (STRCAT h (STRING c "")) = STRLEN h + 1` by fs[]
      \\ `LENGTH (STRCAT h (STRING c "")) = STRLEN ls` by fs[]
      \\ imp_res_tac isPREFIX_EQ_LENGTH \\ `LAST (STRCAT h (STRING c "")) = LAST ls` by metis_tac[]
      \\ fs[LAST_APPEND]))
  >-(imp_res_tac NOT_LESS \\ imp_res_tac FIELDS_full \\ fs[NULL_EQ])
QED

Theorem P_LAST_IMPL_NULL_LAST_FIELDS:
  !ls.
    ls <> [] ==> (P (LAST ls)  ==> NULL (LAST (FIELDS P ls)))
Proof
  completeInduct_on `LENGTH (ls:string)`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `FIELDS P ls` >- fs[FIELDS_NEQ_NIL]
  \\ cases_on `STRLEN h < STRLEN ls`
  >-(imp_res_tac FIELDS_next \\ fs[] \\ cases_on `SUC (STRLEN h) < LENGTH ls`
    >-(`LAST (DROP (SUC (STRLEN h)) ls) = LAST ls` by metis_tac[last_drop]
      \\ rveq \\ `FIELDS P (DROP (SUC (STRLEN h)) ls) <> []` by fs[FIELDS_NEQ_NIL]
      \\ fs[LAST_DEF] \\ last_assum (qspecl_then [`DROP (SUC (STRLEN h)) ls`] mp_tac)
      \\ disch_tac \\ fs[LENGTH_DROP, DROP_NIL])
    >-(fs[DROP_LENGTH_TOO_LONG, FIELDS_def] \\ rveq \\ fs[LAST_DEF]
      \\ imp_res_tac LESS_SUC_NOT \\ imp_res_tac NOT_LESS
      \\ `STRLEN h + 1 = STRLEN ls` by (fs[SUC_ONE_ADD] \\ decide_tac)
      \\ `LENGTH (STRCAT h (STRING c "")) = STRLEN h + STRLEN (STRING c "")` by fs[LENGTH_APPEND]))
  >-(`LENGTH (FIELDS P ls) = LENGTH (FILTER P ls) + 1` by fs[LENGTH_FIELDS]
    \\ imp_res_tac NOT_LESS \\ imp_res_tac FIELDS_full \\ fs[NULL_EQ]
    \\ `LENGTH [ls] = STRLEN (FILTER P ls) + 1` by metis_tac[]
    \\ `1 = STRLEN (FILTER P ls) + 1` by fs[LENGTH]
    \\ `STRLEN (FILTER P ls) = 0` by decide_tac
    \\ `FILTER P ls = []` by fs[LENGTH_NIL] \\ imp_res_tac FILTER_EQ_NIL
    \\ imp_res_tac EVERY_LAST \\ metis_tac[])
QED

Theorem NULL_LAST_FIELDS_THM:
  !P ls.
    ls <> [] ==> (P (LAST ls)  <=> NULL (LAST (FIELDS P ls)))
Proof
  rpt strip_tac
  \\ eq_tac >- fs[P_LAST_IMPL_NULL_LAST_FIELDS] >- fs[NULL_LAST_FIELDS_IMPL_P_LAST]
QED

Theorem EXISTS_dropUntilIncl_right:
  !P ls.
    EXISTS P ls /\ ~P (LAST ls) ==> dropUntilIncl P ls <> []
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[]
  \\ cases_on `t = []` >- fs[LAST_DEF, EXISTS_DEF]
  \\ cases_on `P h`
  >-(fs[LAST_DEF] \\ fs[dropUntilIncl_def, mllistTheory.dropUntil_def] \\ rfs[])
  >-(fs[LAST_DEF, dropUntilIncl_def, mllistTheory.dropUntil_def]
    \\ last_assum (qspecl_then [`t`] mp_tac) \\ disch_tac \\ fs[SUC_ONE_ADD] \\ res_tac)
QED

Theorem EXISTS_dropUntilIncl_left:
  !P ls.
    ls <> [] /\ dropUntilIncl P ls <> [] ==> EXISTS P ls
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[]
  \\ cases_on `P h` >- fs[]
  >-(fs[LAST_DEF, dropUntilIncl_def, mllistTheory.dropUntil_def]
    \\ last_assum (qspecl_then [`t`] mp_tac) \\ disch_tac \\ fs[SUC_ONE_ADD]
    \\ cases_on `t` >- fs[mllistTheory.dropUntil_def]
    \\ res_tac \\ rfs[])
QED

Theorem NOT_EXISTS_FRONT:
  !ls.
    EXISTS P ls /\ ~EXISTS P (FRONT ls) ==> P (LAST ls)
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[]
  \\ cases_on `t = []` >- fs[LAST_DEF, FRONT_DEF]
  \\ fs[LAST_DEF, FRONT_DEF]
QED

Theorem EXISTS_FRONT_dropUntilIncl_neq_nil:
  !ls.
    ls <> [] /\ EXISTS P (FRONT ls) ==> dropUntilIncl P ls <> []
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[]
  \\ cases_on `t = []` >- fs[LAST_DEF, FRONT_DEF]
  \\ cases_on `P h` >- (fs[LAST_DEF, FRONT_DEF, dropUntilIncl_def, mllistTheory.dropUntil_def])
  >-(fs[LAST_DEF, FRONT_DEF, dropUntilIncl_def, mllistTheory.dropUntil_def]
    \\ last_assum (qspecl_then [`t`] mp_tac) \\ disch_tac \\ fs[SUC_ONE_ADD] \\ res_tac)
QED

Theorem NOT_EXISTS_FRONT_dropUntilIncl_eq_nil:
  !ls.
    ls <> [] /\ ~EXISTS P (FRONT ls) ==> dropUntilIncl P ls = []
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[]
  \\ cases_on `t = []`
  >-(Cases_on `P h` >- fs[FRONT_DEF, dropUntilIncl_def, mllistTheory.dropUntil_def]
    \\ fs[FRONT_DEF, dropUntilIncl_def, mllistTheory.dropUntil_def])
  \\ fs[FRONT_DEF, dropUntilIncl_def, mllistTheory.dropUntil_def]
QED

Theorem NOT_EXISTS_FRONT_takeUntil_eq_FRONT:
  !ls.
    EXISTS P ls /\ ~EXISTS P (FRONT ls) ==> takeUntil P ls = FRONT ls
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[]
  \\ cases_on `t = []`
  >-(Cases_on `P h` >- fs[FRONT_DEF, mllistTheory.takeUntil_def]
    \\ fs[FRONT_DEF, mllistTheory.takeUntil_def])
  \\ fs[FRONT_DEF, mllistTheory.takeUntil_def]
QED

Theorem NOT_EXISTS_FRONT_takeUntilIncl_eq_FRONT_LAST:
  !ls.
    EXISTS P ls /\ ~EXISTS P (FRONT ls) ==>
    takeUntilIncl P ls = FRONT ls ++ [LAST ls]
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[]
  \\ cases_on `t = []`
  >-(Cases_on `P h` >- fs[FRONT_DEF, takeUntilIncl_def]
    \\ fs[FRONT_DEF, takeUntilIncl_def])
  \\ fs[FRONT_DEF, LAST_DEF, takeUntilIncl_def]
QED


Theorem EXISTS_takeUntilIncl_APPEND_takeUntil_EL:
  !ls.
    EXISTS P ls ==>
    (takeUntilIncl P ls = takeUntil P ls ++ [EL (LENGTH (takeUntil P ls)) ls] /\
    P (EL (LENGTH (takeUntil P ls)) ls))
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[EXISTS_DEF]
  >-(Cases_on `P h` >- fs[takeUntilIncl_def, mllistTheory.takeUntil_def]
    \\ fs[takeUntilIncl_def, mllistTheory.takeUntil_def])
  >-(fs[EXISTS_DEF])
  \\ Cases_on `P h` >- fs[takeUntilIncl_def, mllistTheory.takeUntil_def]
  \\ fs[takeUntilIncl_def, mllistTheory.takeUntil_def]
QED

Theorem EXISTS_FRONT_dropUntilIncl_thm:
  !P ls.
    ls <> [] ==>
     (EXISTS P (FRONT ls) <=> dropUntilIncl P ls <> [])
Proof
  rpt strip_tac \\ eq_tac
  >-(metis_tac[EXISTS_FRONT_dropUntilIncl_neq_nil])
  \\ metis_tac[NOT_EXISTS_FRONT_dropUntilIncl_eq_nil]
QED

Theorem EXISTS_FRONT_LAST_dropUntilIncl_eq:
  !P ls.
    ls <> [] /\ EXISTS P (FRONT ls) ==> LAST (dropUntilIncl P ls) = LAST ls
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[]
  \\ cases_on `t = []` >- fs[LAST_DEF, FRONT_DEF]
  \\ cases_on `P h` >- (fs[LAST_DEF, FRONT_DEF, dropUntilIncl_def, mllistTheory.dropUntil_def])
  >-(fs[LAST_DEF, FRONT_DEF, dropUntilIncl_def, mllistTheory.dropUntil_def])
QED

Theorem LENGTH_FILTER_dropUntilIncl_one_less:
  !ls.
    ls <> [] /\ EXISTS P (FRONT ls) ==>
      LENGTH (FILTER P (dropUntilIncl P ls)) = LENGTH (FILTER P ls) - 1
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[]
  \\ cases_on `t = []` >- fs[FRONT_DEF]
  \\ cases_on `P h` >- (fs[FILTER, FRONT_DEF, dropUntilIncl_def, mllistTheory.dropUntil_def])
  >-(fs[FILTER, FRONT_DEF, dropUntilIncl_def, mllistTheory.dropUntil_def])
QED

Theorem LENGTH_FILTER_dropUntilIncl:
  !ls.
    ls <> [] /\ EXISTS P (FRONT ls) ==>
      LENGTH (FILTER P (dropUntilIncl P ls)) < LENGTH (FILTER P ls)
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[]
  \\ cases_on `t = []` >- fs[FRONT_DEF]
  \\ cases_on `P h` >- (fs[FILTER, FRONT_DEF, dropUntilIncl_def, mllistTheory.dropUntil_def])
  >-(fs[FILTER, FRONT_DEF, dropUntilIncl_def, mllistTheory.dropUntil_def])
QED

Theorem NOT_EXISTS_FRONT_FILTER:
  !ls.
    ls <> [] /\ ~EXISTS P (FRONT ls) /\ EXISTS P ls  ==>
      FILTER P ls = [LAST ls]
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[]
  \\ cases_on `t = []` >- fs[FRONT_DEF]
  \\ cases_on `P h` >- (fs[FILTER, FRONT_DEF])
  >-(fs[FILTER, LAST_DEF, FRONT_DEF])
QED

Theorem LENGTH_splitlines_dropUntilIncl:
  !ls n.
      EXISTS ($= #"\n") ls ==>
      LENGTH (splitlines (dropUntilIncl ($= #"\n") ls)) < LENGTH (splitlines ls)
Proof
  completeInduct_on `LENGTH (ls:string)`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls = []` >- fs[EXISTS_DEF]
  \\ cases_on `EXISTS ($= #"\n") (FRONT ls)`
  >-(Cases_on `NULL (LAST (FIELDS ($= #"\n") (dropUntilIncl ($= #"\n") ls)))`
  >-(Cases_on `NULL (LAST (FIELDS ($= #"\n") ls))`
    >-(fs[SUC_ONE_ADD,LENGTH_splitlines, LENGTH_FILTER_dropUntilIncl])
    >-(fs[SUC_ONE_ADD,LENGTH_splitlines]
      \\ `LENGTH (FILTER ($= #"\n") (dropUntilIncl ($= #"\n") ls)) <
            LENGTH (FILTER ($= #"\n") ls)` by metis_tac[LENGTH_FILTER_dropUntilIncl]
      \\ decide_tac))
  >-(`dropUntilIncl ($= #"\n") ls <> []` by fs[EXISTS_FRONT_dropUntilIncl_neq_nil]
    \\ assume_tac NULL_LAST_FIELDS_THM
    \\ pop_assum (qspecl_then [`($= #"\n")`, `(dropUntilIncl ($= #"\n") ls)`] mp_tac) \\ disch_tac
    \\ res_tac \\ `~($= #"\n") (LAST (dropUntilIncl ($= #"\n") ls))` by metis_tac[]
    \\ `LAST (dropUntilIncl ($= #"\n") ls) = LAST ls` by fs[EXISTS_FRONT_LAST_dropUntilIncl_eq]
    \\ `~($= #"\n") (LAST ls)` by metis_tac[]
    \\ Cases_on `NULL (LAST (FIELDS ($= #"\n") ls))`
    >-(qpat_x_assum `#"\n" ≠ LAST ls` mp_tac
      \\ assume_tac NULL_LAST_FIELDS_THM
      \\ pop_assum (qspecl_then [`($= #"\n")`, `ls`] mp_tac) \\ disch_tac
      \\ res_tac \\ strip_tac)
    >-(fs[SUC_ONE_ADD,LENGTH_splitlines, LENGTH_FILTER_dropUntilIncl])))
  \\ imp_res_tac NOT_EXISTS_FRONT \\ imp_res_tac NULL_LAST_FIELDS_THM
  \\ Cases_on `dropUntilIncl ($= #"\n") ls`
  >-(fs[LENGTH_splitlines, FILTER, LENGTH_FILTER_EXISTS])
  \\ pop_assum mp_tac \\ `dropUntilIncl ($= #"\n") ls = []` by metis_tac[EXISTS_FRONT_dropUntilIncl_thm]
  \\ strip_tac \\ fs[]
QED

Theorem LENGTH_splitlines_dropUntilIncl_one_less:
  !ls n.
      EXISTS ($= #"\n") ls ==>
      LENGTH (splitlines (dropUntilIncl ($= #"\n") ls)) = LENGTH (splitlines ls) - 1
Proof
  completeInduct_on `LENGTH (ls:string)`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls = []` >- fs[EXISTS_DEF]
  \\ cases_on `EXISTS ($= #"\n") (FRONT ls)`
  >-(imp_res_tac EXISTS_FRONT_LAST_dropUntilIncl_eq
    \\ `dropUntilIncl ($= #"\n") ls <> []` by fs[EXISTS_FRONT_dropUntilIncl_neq_nil]
    \\ Cases_on `($= #"\n") (LAST (dropUntilIncl ($= #"\n") ls))`
    >-(`($= #"\n") (LAST ls)` by rfs[]
      \\ `NULL (LAST (FIELDS ($= #"\n") ls))`
            by (imp_res_tac P_LAST_IMPL_NULL_LAST_FIELDS \\ rfs[])
      \\ qpat_x_assum `LAST _ = _` kall_tac \\ qpat_x_assum ` #"\n" = LAST ls` kall_tac
      \\ assume_tac NULL_LAST_FIELDS_THM \\ pop_assum
            (qspecl_then [`($= #"\n")`, `dropUntilIncl ($= #"\n") ls`] mp_tac)
      \\ strip_tac \\ rfs[] \\ simp[LENGTH_splitlines, LENGTH_FILTER_dropUntilIncl_one_less])
    >-(`~($= #"\n") (LAST ls)` by metis_tac[]
      \\ qpat_x_assum `LAST _ = LAST _` kall_tac
      \\ assume_tac NULL_LAST_FIELDS_THM \\ pop_assum
            (qspecl_then [`($= #"\n")`, `dropUntilIncl ($= #"\n") ls`] mp_tac) \\ strip_tac
      \\ assume_tac NULL_LAST_FIELDS_THM \\ pop_assum
            (qspecl_then [`($= #"\n")`, `ls`] mp_tac) \\ strip_tac
      \\ `~NULL (LAST (FIELDS ($= #"\n") (dropUntilIncl ($= #"\n") ls)))` by metis_tac[]
      \\ `~NULL (LAST (FIELDS ($= #"\n") ls))` by metis_tac[]
      \\ `0 < STRLEN (FILTER ($= #"\n") ls)` by fs[LENGTH_FILTER_EXISTS]
      \\ simp[LENGTH_splitlines, LENGTH_FILTER_dropUntilIncl_one_less]))
  >-(imp_res_tac NOT_EXISTS_FRONT \\ fs[NOT_EXISTS_FRONT_dropUntilIncl_eq_nil]
    \\ `NULL (LAST (FIELDS ($= #"\n") ls))`
            by (imp_res_tac P_LAST_IMPL_NULL_LAST_FIELDS \\ rfs[])
    \\ `~EXISTS ($= (LAST ls)) (FRONT ls)` by metis_tac[EXISTS_NOT_EVERY]
    \\ fs[LENGTH_splitlines, NOT_EXISTS_FRONT_FILTER])
QED

Theorem DROP_LENGTH_takeUntil_eq_dropUntil:
  !ls.
     DROP (LENGTH (takeUntil P ls)) ls = dropUntil P ls
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[mllistTheory.dropUntil_def, mllistTheory.takeUntil_def]
  \\ cases_on `P h` >- (fs[mllistTheory.dropUntil_def, mllistTheory.takeUntil_def])
  >-(fs[mllistTheory.dropUntil_def, mllistTheory.takeUntil_def])
QED

Theorem LENGTH_splitlines_append_exists_r:
  !ls rs.
      ~EXISTS ($= #"\n") ls /\ EXISTS ($= #"\n") rs ==>
        LENGTH (splitlines (STRCAT ls rs)) = LENGTH (splitlines rs)
Proof
  completeInduct_on `LENGTH (ls:string)`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ `~NULL rs` by (cases_on `rs` >- fs[EXISTS_DEF] >- fs[NULL_EQ])
  \\ `~NULL (STRCAT ls rs)` by fs[NULL_APPEND]
  \\ ` ~EXISTS ($= #"\n") ls` by metis_tac[EXISTS_NOT_EVERY]
  \\ simp[splitlines_append_not_exists_l]
  \\ ntac 3 (pop_assum kall_tac)
  \\ `DROP (SUC (STRLEN (takeUntil ($= #"\n") rs))) rs =
      DROP 1 (DROP (STRLEN (takeUntil ($= #"\n") rs)) rs)` by fs[SUC_ONE_ADD, DROP_DROP_T]
  \\ rw[] \\ fs[DROP_LENGTH_takeUntil_eq_dropUntil, GSYM dropUntilIncl_def]
  \\ fs[LENGTH_splitlines_dropUntilIncl_one_less, SUC_ONE_ADD]
  \\ cases_on `rs = []` >-fs[EXISTS_DEF]
  \\ `splitlines rs <> []` by metis_tac[splitlines_eq_nil]
  \\ `1 <= LENGTH (splitlines rs)` by fs[NOT_NIL_EQ_LENGTH_NOT_0]
  \\ fs[]
QED

Theorem LENGTH_splitlines_append_same:
  !ls rs.
    ls <> [] /\ LAST ls = LAST rs /\
    LENGTH (splitlines ls) < LENGTH (splitlines rs) ==>
        LENGTH (splitlines (ls ++ xs)) < LENGTH (splitlines (rs ++ xs))
Proof
  rpt strip_tac
  \\ Cases_on `xs` >- rw[]
  \\ cases_on `ls` >- fs[]
  \\ cases_on `rs` >- fs[splitlines_def]
  \\ qabbrev_tac `ls = STRING h' t'`
  \\ qabbrev_tac `rs = STRING h'' t''`
  \\ qabbrev_tac `xs = STRING h t`
  \\ `LAST (ls ++ xs) = LAST xs` by fs[LAST_APPEND, Abbr`xs`]
  \\ `LAST (rs ++ xs) = LAST xs` by fs[LAST_APPEND, Abbr`xs`]
  \\ Cases_on `($= #"\n") (LAST xs)`
  >-(`($= #"\n") (LAST (STRCAT ls xs))` by fs[]
    \\ `($= #"\n") (LAST (STRCAT rs xs))` by fs[]
    \\ `STRCAT ls xs <> []` by fs[] \\ `STRCAT rs xs <> []` by fs[Abbr`rs`,Abbr`xs`]
    \\ imp_res_tac P_LAST_IMPL_NULL_LAST_FIELDS \\ pop_assum kall_tac
    \\ qpat_x_assum `LAST (STRCAT ls xs) = LAST xs` kall_tac
    \\ qpat_x_assum `LAST (STRCAT rs xs) = LAST xs` kall_tac
    \\ qpat_x_assum `#"\n" = LAST xs` kall_tac
    \\ qpat_x_assum `#"\n" = LAST (STRCAT ls xs)` kall_tac
    \\ qpat_x_assum `#"\n" = LAST (STRCAT rs xs)` kall_tac
    \\ qpat_x_assum `STRCAT ls xs ≠ ""` kall_tac
    \\ qpat_x_assum `STRCAT rs xs ≠ ""` kall_tac
    \\ `rs <> []` by fs[Abbr`rs`]
    \\ fs[LENGTH_splitlines, FILTER_APPEND]
    >-(Cases_on `($= #"\n") (LAST ls)`
      >-(`($= #"\n") (LAST rs)` by fs[] \\ imp_res_tac P_LAST_IMPL_NULL_LAST_FIELDS
        \\ fs[LENGTH_splitlines])
      >-(`~($= #"\n") (LAST rs)` by metis_tac[]
        \\ assume_tac NULL_LAST_FIELDS_THM
        \\ pop_assum (qspecl_then [`($= #"\n")`, `ls`] mp_tac) \\ disch_tac
        \\ assume_tac NULL_LAST_FIELDS_THM
        \\ pop_assum (qspecl_then [`($= #"\n")`, `rs`] mp_tac) \\ disch_tac
        \\ res_tac \\ `~(NULL (LAST (FIELDS ($= #"\n") ls)))` by metis_tac[]
        \\ `~(NULL (LAST (FIELDS ($= #"\n") rs)))` by metis_tac[]
        \\ fs[LENGTH_splitlines])))
  >-(`~($= #"\n") (LAST (STRCAT ls xs))` by fs[]
    \\ `~($= #"\n") (LAST (STRCAT rs xs))` by fs[]
    \\ `STRCAT ls xs <> []` by fs[] \\ `STRCAT rs xs <> []` by fs[Abbr`rs`,Abbr`xs`]
    \\ assume_tac NULL_LAST_FIELDS_THM
    \\ pop_assum (qspecl_then [`($= #"\n")`, `STRCAT ls xs`] mp_tac) \\ disch_tac
    \\ assume_tac NULL_LAST_FIELDS_THM
    \\ pop_assum (qspecl_then [`($= #"\n")`, `STRCAT rs xs`] mp_tac) \\ disch_tac
    \\ res_tac \\ `~(NULL (LAST (FIELDS ($= #"\n") (STRCAT ls xs))))` by metis_tac[]
    \\ `~(NULL (LAST (FIELDS ($= #"\n") (STRCAT rs xs))))` by metis_tac[]
    \\ qpat_x_assum `LAST (STRCAT ls xs) = LAST xs` kall_tac
    \\ qpat_x_assum `LAST (STRCAT rs xs) = LAST xs` kall_tac
    \\ qpat_x_assum `#"\n" ≠ LAST xs` kall_tac
    \\ qpat_x_assum `#"\n" ≠ LAST (STRCAT ls xs)` kall_tac
    \\ qpat_x_assum `#"\n" ≠ LAST (STRCAT rs xs)` kall_tac
    \\ qpat_x_assum `STRCAT ls xs ≠ ""` kall_tac
    \\ qpat_x_assum `STRCAT rs xs ≠ ""` kall_tac
    \\ ntac 2 (pop_assum mp_tac) \\ ntac 8 (pop_assum kall_tac) \\ rpt strip_tac
    \\ `rs <> []` by fs[Abbr`rs`]
    \\ fs[LENGTH_splitlines, FILTER_APPEND]
    >-(Cases_on `($= #"\n") (LAST ls)`
      >-(`($= #"\n") (LAST rs)` by fs[] \\ imp_res_tac P_LAST_IMPL_NULL_LAST_FIELDS
        \\ fs[LENGTH_splitlines])
      >-(`~($= #"\n") (LAST rs)` by metis_tac[]
        \\ assume_tac NULL_LAST_FIELDS_THM
        \\ pop_assum (qspecl_then [`($= #"\n")`, `ls`] mp_tac) \\ disch_tac
        \\ assume_tac NULL_LAST_FIELDS_THM
        \\ pop_assum (qspecl_then [`($= #"\n")`, `rs`] mp_tac) \\ disch_tac
        \\ res_tac \\ `~(NULL (LAST (FIELDS ($= #"\n") ls)))` by metis_tac[]
        \\ `~(NULL (LAST (FIELDS ($= #"\n") rs)))` by metis_tac[]
        \\ fs[LENGTH_splitlines])))
QED

Theorem dropUntilIncl_eq_TL_dropUntil:
  !ls.
    dropUntil P ls <> [] ==>
    dropUntilIncl P ls = TL (dropUntil P ls)
Proof
  fs[dropUntilIncl_def]
  \\ Cases_on `dropUntil P ls` >- fs[]
  \\ strip_tac \\ simp[DROP, TL]
QED

Theorem DROP_SUC_DROP_1_DROP:
  !ls n.
    DROP (SUC n) ls = DROP 1 (DROP n ls)
Proof
  fs[SUC_ONE_ADD, DROP_DROP_T]
QED

Theorem isPREFIX_TAKE_LENGTH:
  !ls rs.
    ls ≼ rs <=> (ls = TAKE (LENGTH ls) rs /\ LENGTH ls <= LENGTH rs)
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ eq_tac
  >-(cases_on `ls` >- fs[TAKE_0]
    \\ cases_on `rs` >- fs[isPREFIX]
    \\ fs[isPREFIX, TAKE])
  >-(cases_on `ls` >- fs[TAKE_0]
    \\ cases_on `rs` >- fs[isPREFIX]
    \\ fs[isPREFIX, TAKE])
QED

Theorem isPREFIX_LENGTH_LEQ:
  !ls rs.
    ls ≼ rs ==> LENGTH ls <= LENGTH rs
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[]
  \\ cases_on `rs` >- fs[isPREFIX]
  \\ fs[isPREFIX, LENGTH]
QED

Theorem isPREFIX_SEG:
  !ls rs.
    ls ≼ rs <=>
      ls = SEG (LENGTH ls) 0 rs /\ LENGTH ls <= LENGTH rs
Proof
  rpt strip_tac
  \\ eq_tac
  >-(rpt strip_tac \\ imp_res_tac isPREFIX_TAKE_LENGTH
    \\ `LENGTH ls <= LENGTH rs` by fs[isPREFIX_LENGTH_LEQ]
    \\ fs[TAKE_SEG])
  \\ rpt strip_tac
  \\ fs[GSYM TAKE_SEG]
  \\ fs[isPREFIX_TAKE_LENGTH]
QED

Theorem SEG_dropUntilIncl_SEG_takeUntilIncl:
  !ls.
     SEG n 0 (dropUntilIncl P ls) = SEG n (LENGTH (takeUntilIncl P ls)) ls
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[dropUntilIncl_def, mllistTheory.dropUntil_def, takeUntilIncl_def]
  \\ cases_on `P h`
  >-(fs[dropUntilIncl_def, mllistTheory.dropUntil_def, takeUntilIncl_def]
    \\ cases_on `n` >- fs[SEG]
    \\ `SUC 0 = 1` by fs[]
    \\ `SEG (SUC n') 1 (h::t) = SEG (SUC n') (SUC 0) (h::t)` by fs[]
    \\ qpat_x_assum `SUC 0 = _` kall_tac \\ fs[SEG])
  \\ fs[dropUntilIncl_def, mllistTheory.dropUntil_def, takeUntilIncl_def]
  \\ cases_on `n` >- fs[SEG] >- fs[SEG]
QED

Theorem isPREFIX_dropUntilIncl_eq_SEG_LENGTH_takeUntilIncl:
  !ls rs.
    ls ≼ dropUntilIncl P rs ==>
      ls = SEG (LENGTH ls) (LENGTH (takeUntilIncl P rs)) rs
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ imp_res_tac isPREFIX_SEG
  \\ `LENGTH rs = LENGTH (dropUntilIncl P rs) + LENGTH (takeUntilIncl P rs)`
        by fs[LENGTH_dropUntilIncl_takeUntilIncl]
  \\ `LENGTH (dropUntilIncl P rs) <= LENGTH rs` by fs[LENGTH_dropUntilIncl]
  \\ `LENGTH (takeUntilIncl P rs) = LENGTH rs - LENGTH (dropUntilIncl P rs)`
      by decide_tac \\ qpat_x_assum `LENGTH rs = _` kall_tac
  \\ cases_on `ls` >- fs[SEG]
  \\ cases_on `rs` >- fs[dropUntilIncl_def, mllistTheory.dropUntil_def,isPREFIX]
  \\ cases_on `P h'`
  >-(fs[dropUntilIncl_def, mllistTheory.dropUntil_def, takeUntilIncl_def,
        LENGTH, SEG, isPREFIX]
    \\ `SEG (SUC (LENGTH t)) (SUC 0) (h'::t') = SEG (SUC (LENGTH t)) 0 t'` by metis_tac[SEG]
    \\ fs[SUC_ONE_ADD])
  \\ fs[dropUntilIncl_def, mllistTheory.dropUntil_def, takeUntilIncl_def,
        isPREFIX]
  \\ `SUC (LENGTH t') − (LENGTH (dropUntil P t') − 1) = SUC (LENGTH (takeUntilIncl P t'))`
        by decide_tac
  \\ qpat_x_assum `SUC _ = SUC _ - _` kall_tac
  \\ `SUC (LENGTH t) + 1 ≤ LENGTH (dropUntil P t')` by decide_tac
  \\ `SUC (LENGTH t') + 1 − LENGTH (dropUntil P t') =
        SUC (LENGTH t' + 1 − LENGTH (dropUntil P t'))`
        by fs[] \\ rw[] \\ fs[SEG]
  \\ fs[GSYM dropUntilIncl_def, SEG_dropUntilIncl_SEG_takeUntilIncl]
QED

Theorem dropUntilIncl_takeUntilIncl:
  !ls.
    dropUntilIncl P ls = DROP (LENGTH (takeUntilIncl P ls)) ls
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[dropUntilIncl_def, mllistTheory.dropUntil_def, takeUntilIncl_def]
  \\ cases_on `P h`
  >-(fs[dropUntilIncl_def, mllistTheory.dropUntil_def, takeUntilIncl_def])
  \\ fs[dropUntilIncl_def, mllistTheory.dropUntil_def, takeUntilIncl_def]
QED

Theorem SEG_APPEND_part_of_DROP:
  !ls n k.
    ls <> [] /\ n + k <= LENGTH ls ==>
      SEG n k ls ++ (DROP (n + k) ls) = DROP k ls
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[]
  \\ cases_on `k + n` >- fs[SEG]
  \\ cases_on `n` >- fs[SEG]
  \\ cases_on  `k` >- fs[SEG, SEG_TAKE_DROP]
  \\ fs[SEG, DROP]
  \\ cases_on `t = []` >- fs[]
  \\ fs[SUC_ONE_ADD] \\ `n' = n + n'' + 1` by decide_tac
  \\ last_assum (qspecl_then [`t`, `n'' + 1`,`n`] mp_tac)
  \\ disch_tac \\ fs[]
QED

Theorem isPREFIX_MAP:
  !ls rs.
    ls ≼ rs ==> MAP f ls ≼ MAP f rs
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[]
  \\ cases_on `rs` >- fs[isPREFIX]
  \\ fs[MAP]
  \\ last_assum (qspecl_then [`t`,`t'`] mp_tac) \\ disch_tac
  \\ fs[]
QED

Theorem LENGTH_takeUntilIncl_DROP_PREFIX:
  !ls xs.
    ~EXISTS P xs /\ xs ≼ ls ==>
      LENGTH (takeUntilIncl P (DROP (LENGTH xs) ls)) =
      LENGTH (DROP (LENGTH xs) (takeUntilIncl P ls))
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ reverse (cases_on `LENGTH xs <= LENGTH ls`)
  >-(fs[DROP_LENGTH_TOO_LONG, takeUntilIncl_def]
    \\ `LENGTH (takeUntilIncl P ls) <= LENGTH ls` by fs[takeUntilIncl_length_leq]
    \\ rfs[])
  \\ cases_on `ls` >- fs[EXISTS_DEF, takeUntilIncl_def]
  \\ cases_on `xs` >- fs[]
  \\ fs[DROP, isPREFIX_THM]
  \\ cases_on `P h` >- fs[EXISTS_DEF, takeUntilIncl_def]
  \\ fs[takeUntilIncl_def]
QED

Theorem takeUntilIncl_eq_takeUntil_append:
  !ls c.
    EXISTS ($= c) ls /\ ($= c) a ==>
      takeUntilIncl ($= c) ls = takeUntil ($= c) ls ++ [a]
Proof
  completeInduct_on `LENGTH ls`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ cases_on `ls` >- fs[dropUntilIncl_def, mllistTheory.dropUntil_def, takeUntilIncl_def]
  \\ cases_on `($= a) h`
  >-(fs[mllistTheory.takeUntil_def, takeUntilIncl_def])
  \\ fs[mllistTheory.takeUntil_def, takeUntilIncl_def]
QED

Theorem forwardFD_lineForwardFD_not_in_buffer:
  !buff fs fd extra.
    get_file_content fs fd = SOME (content, pos) /\
    (extra ≼ dropUntilIncl ($= (10w:word8)) (MAP (n2w:num->word8 o ORD) (DROP pos content)) \/
     extra = []) /\
    ~EXISTS ($= (10w:word8)) buff ==>
      (forwardFD fs fd (LENGTH extra + LENGTH (takeUntilIncl ($= #"\n") (DROP pos content))) =
        lineForwardFD buff fs fd extra)
Proof
  rpt strip_tac \\ simp[lineForwardFD_def]
  >-(cases_on `pos < STRLEN content`
    >-(simp[SPLITP_takeUntil_dropUntil]
      \\ cases_on `EXISTS ($= #"\n") (DROP pos content)`
      >-(`dropUntil ($= #"\n") (DROP pos content) <> []` by fs[dropUntil_length_gt_0, NOT_NIL_EQ_LENGTH_NOT_0]
        \\ simp[NULL_EQ] \\ imp_res_tac LENGTH_takeUntil_takeUntilIncl
        \\ fs[SUC_ONE_ADD])
      \\ `LENGTH (dropUntil ($= #"\n") (DROP pos content)) = 0` by metis_tac[LENGTH_dropUntil]
      \\ fs[takeUntilIncl_not_exists, takeUntil_not_exists])
    \\ fs[DROP_LENGTH_TOO_LONG, isPREFIX, fastForwardFD_0, dropUntilIncl_def, mllistTheory.dropUntil_def,
          takeUntilIncl_def])
  >-(cases_on `pos < STRLEN content`
    >-(simp[SPLITP_takeUntil_dropUntil]
      \\ cases_on `EXISTS ($= #"\n") (DROP pos content)`
      >-(`dropUntil ($= #"\n") (DROP pos content) <> []` by fs[dropUntil_length_gt_0, NOT_NIL_EQ_LENGTH_NOT_0]
        \\ simp[NULL_EQ] \\ imp_res_tac LENGTH_takeUntil_takeUntilIncl
        \\ fs[SUC_ONE_ADD])
      \\ `LENGTH (dropUntil ($= #"\n") (DROP pos content)) = 0` by metis_tac[LENGTH_dropUntil]
      \\ fs[takeUntilIncl_not_exists, takeUntil_not_exists])
    \\ fs[DROP_LENGTH_TOO_LONG, isPREFIX, fastForwardFD_0, dropUntilIncl_def, mllistTheory.dropUntil_def,
          takeUntilIncl_def])
QED

Theorem input_aux_w_content_spec:
  !len lenv outbuf is.
  NUM len lenv /\ NUM off offv  /\ len + off <= LENGTH outcont /\
  len <= LENGTH bactive ==>
  app (p:'ffi ffi_proj) TextIO_input_aux_v [is;outbuf;offv;lenv]
  (W8ARRAY outbuf outcont * INSTREAM_BUFFERED_BL_FD bcontent bactive fd is)
  (POSTv nReadv. &(NUM len nReadv) *
                  W8ARRAY outbuf
                    (insert_atI (TAKE len bactive) off outcont) *
                  INSTREAM_BUFFERED_BL_FD bcontent (DROP len bactive) fd is)
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_input_aux_v_def
  \\ fs[INSTREAM_BUFFERED_BL_FD_def, REF_NUM_def] \\ xpull
  \\ xmatch \\ xlet_auto >- xsimpl
  \\ fs[instream_buffered_inv_def]
  \\ xlet_auto >-xsimpl
  \\ xlet_auto >-xsimpl
  \\ xlet_auto >-xsimpl
  \\ xvar \\ xsimpl
  \\ map_every qexists_tac [`r+len`,`w`] \\ fs[]
  \\ conj_tac
  >-(simp[DROP_SEG, TAKE_SEG]
    \\ simp[SEG_SEG])
  >-(fs[DROP_NIL,insert_atI_def]
    \\ simp[DROP_SEG, TAKE_SEG]
    \\ simp[SEG_SEG])
QED

Theorem input_aux_spec:
  !len lenv outbuf is.
  NUM len lenv /\ NUM off offv  /\ len + off <= LENGTH outcont /\
  len <= LENGTH bactive ==>
  app (p:'ffi ffi_proj) TextIO_input_aux_v [is;outbuf;offv;lenv]
  (W8ARRAY outbuf outcont * INSTREAM_BUFFERED_FD bactive fd is)
  (POSTv nReadv. &(NUM len nReadv) *
                  W8ARRAY outbuf
                    (insert_atI (TAKE len bactive) off outcont) *
                  INSTREAM_BUFFERED_FD (DROP len bactive) fd is)
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_input_aux_v_def
  \\ fs[INSTREAM_BUFFERED_FD_def, REF_NUM_def] \\ xpull
  \\ xmatch \\ xlet_auto >- xsimpl
  \\ fs[instream_buffered_inv_def]
  \\ xlet_auto >-xsimpl
  \\ xlet_auto >-xsimpl
  \\ xlet_auto >-xsimpl
  \\ xvar \\ xsimpl
  \\ map_every qexists_tac [`r+len`,`w`] \\ fs[]
  \\ conj_tac
  >-(simp[DROP_SEG, TAKE_SEG]
    \\ simp[SEG_SEG])
  >-(fs[DROP_NIL,insert_atI_def]
    \\ simp[DROP_SEG, TAKE_SEG]
    \\ simp[SEG_SEG])
QED

Theorem input_spec:
  !fd fdv fs content pos off offv req reqv buf bufv bactive pbactive.
  NUM off offv ∧ NUM req reqv ∧
  get_file_content fs fd = SOME(content, pos) ⇒
  get_mode fs fd = SOME ReadMode ⇒
  app (p:'ffi ffi_proj) TextIO_input_v [is; bufv; offv; reqv]
  (STDIO fs * W8ARRAY bufv buf * INSTREAM_BUFFERED_FD bactive fd is)
  (POSTve
    (\nv. SEP_EXISTS pbactive.
      &(NUM (MIN req ((LENGTH content - pos) + LENGTH bactive)) nv /\
        req + off <= LENGTH buf) *
      INSTREAM_BUFFERED_FD pbactive fd is *
      W8ARRAY bufv (insert_atI (TAKE req bactive ++ TAKE (req - LENGTH bactive)
                                             (DROP pos (MAP (n2w o ORD) content)))
                                 off buf) *
      STDIO (fsupdate fs fd 0 (MIN (req + LENGTH pbactive - LENGTH bactive + pos)
                                  (MAX pos (LENGTH content))) content))
    (\e. &(IllegalArgument_exn e /\ LENGTH buf < req + off) *
          STDIO fs * W8ARRAY bufv buf * INSTREAM_BUFFERED_FD bactive fd is))
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_input_v_def
  \\ fs[INSTREAM_BUFFERED_FD_def, REF_NUM_def]
  \\ xpull \\ xmatch
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ fs[NUM_def] \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- (xsimpl \\ qexists_tac `buf` \\ xsimpl)
  \\ xlet_auto >- xsimpl \\ fs[GSYM NUM_def]
  \\ fs[instream_buffered_inv_def]
  \\ `INT (&(w-r)) iv`
        by rfs[INT_OF_NUM_SUBS_2] \\ rfs[GSYM NUM_def]
  \\ xif
  >-(xlet_auto >- (xcon >> xsimpl)
     \\ xraise
     \\ xsimpl \\ map_every qexists_tac [`r`,`w`]
     \\ simp[IllegalArgument_exn_def])
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xif
    >-(`w-r <= LENGTH bactive` by fs[LENGTH_TAKE]
      \\ `LENGTH bactive <= LENGTH bcontent - 4` by fs[LENGTH_TAKE]
      \\ ` w ≤ r + LENGTH (TAKE (w − r) (DROP r bcontent))` by fs[LENGTH_TAKE]
      \\ `w-r <= LENGTH bcontent - 4` by fs[]
      \\ `LENGTH bcontent - 4 < req`
          by (fs[INT_SUB_CALCULATE, INT_ADD_CALCULATE] \\ rfs[])
      \\ `w-r <= req` by fs[] \\ `w-r + off <= LENGTH buf` by fs[]
      \\ xlet `POSTv dc. W8ARRAY bufv
               (insert_atI (TAKE (w-r) bactive)
                  off buf) * INSTREAM_BUFFERED_FD
                              (DROP (w-r) bactive) fd is *
               STDIO fs`
      >-(xapp \\ fs[INSTREAM_BUFFERED_def,INSTREAM_BUFFERED_FD_def,
                    instream_buffered_inv_def] \\ xsimpl
        \\ fs[PULL_EXISTS] \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
        \\ map_every qexists_tac [`w`,`r`,`fd`, `(w-r)`, `off`]
        \\ fs[REF_NUM_def] \\ xsimpl
        \\ fs[INSTREAM_BUFFERED_FD_def, REF_NUM_def, instream_buffered_inv_def]
        \\ rpt strip_tac \\ xsimpl \\ qexists_tac `x'3'` \\ `x'3' = x'` by fs[]
        \\ rveq \\ xsimpl \\ qexists_tac `x'` \\ xsimpl)
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ xlet_auto_spec (SOME raw_input_spec)
      \\ simp[insert_atI_def] \\ xsimpl \\ fs[INT_SUB_CALCULATE,
                                            INT_ADD_CALCULATE]
      \\ fs[INSTREAM_BUFFERED_FD_def, REF_NUM_def,instream_buffered_inv_def]
      \\ xpull \\ xapp \\ xsimpl \\ fs[NUM_def]
      \\ asm_exists_tac \\ qexists_tac `&(w-r)` \\ fs[] \\ rpt strip_tac
      \\ `INT (&MIN req (STRLEN content − pos + (w − r))) v'⁴'`
            by  (pop_assum mp_tac
                \\ simp[INT_SUB_CALCULATE, INT_ADD_CALCULATE]
                \\ simp[MIN_DEF]
                \\ CASE_TAC
                >-(simp[MIN_DEF])
                >-(CASE_TAC
                  >-(fs[])
                  >-(`w + (STRLEN content − pos) − r = STRLEN content − pos + (w − r)`
                          by decide_tac
                    \\ fs[]))) \\ fs[]
      \\ `r' = w'` by fs[]
      \\ fs[MIN_DEF,MAX_DEF] \\ map_every qexists_tac [`w'`,`r'`]
      \\ Cases_on `req < w - r + (STRLEN content - pos) /\ 0 < STRLEN content - pos`
      >-(fs[]
        \\ Cases_on `req < STRLEN content - pos`
        >-(xsimpl \\ simp[TAKE_TAKE, insert_atI_def, LENGTH_TAKE, TAKE_APPEND2]
          \\ `pos < LENGTH (MAP (n2w ∘ ORD) content)` by fs[]
          \\ `LENGTH bcontent - 4 < req`
                by (fs[INT_SUB_CALCULATE, INT_ADD_CALCULATE] \\ rfs[])
          \\ `w-r <= req` by fs[]
          \\ `w-r <= LENGTH bcontent - 4` by fs[]
          \\ fs[TAKE_TAKE_MIN, MIN_DEF]
          \\ fs[DROP_NIL,LENGTH_TAKE, LENGTH_DROP, LENGTH_APPEND, TAKE_APPEND,
                    TAKE_APPEND1, TAKE_APPEND2, DROP_APPEND, DROP_APPEND1, DROP_APPEND2,
                    DROP_DROP])
        >-(fs[]
          \\ `LENGTH content - pos <= req` by fs[]
          \\ `LENGTH bcontent - 4 < req`
                 by (fs[INT_SUB_CALCULATE, INT_ADD_CALCULATE] \\ rfs[])
          \\ `w-r <= req` by fs[]
          \\ `w-r > 0` by fs[]
          \\ `w − r + (STRLEN content − pos) >= STRLEN content - pos` by fs[]
          \\ `req - (w-r) < STRLEN content - pos` by fs[LESS_ADD]
          \\ xsimpl \\ simp[TAKE_TAKE, insert_atI_def, LENGTH_TAKE, TAKE_APPEND2]
          \\ fs[TAKE_TAKE_MIN, MIN_DEF]
          \\ fs[DROP_NIL,LENGTH_TAKE, LENGTH_DROP, LENGTH_APPEND, TAKE_APPEND,
                    TAKE_APPEND1, TAKE_APPEND2, DROP_APPEND, DROP_APPEND1, DROP_APPEND2,
                    DROP_DROP]))
      >-(fs[]
          \\ `LENGTH content - pos <= req` by fs[]
          \\ `LENGTH bcontent - 4 < req`
                 by (fs[INT_SUB_CALCULATE, INT_ADD_CALCULATE] \\ rfs[])
          \\ `w-r <= req` by fs[]
          \\ `w-r >= 0` by fs[]
          \\ `w − r + (STRLEN content − pos) >= STRLEN content - pos` by fs[]
          \\ xsimpl \\ simp[TAKE_TAKE, insert_atI_def, LENGTH_TAKE, TAKE_APPEND2]
          \\ fs[TAKE_TAKE_MIN, MIN_DEF]
          \\ fs[DROP_LENGTH_TOO_LONG,DROP_NIL,LENGTH_TAKE, LENGTH_DROP, LENGTH_APPEND, TAKE_APPEND,
                    TAKE_APPEND1, TAKE_APPEND2, DROP_APPEND, DROP_APPEND1, DROP_APPEND2,
                    DROP_DROP_T]))
  \\ xlet_auto >- xsimpl
  \\ reverse xif \\ fs []
  >-(xapp \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
    \\ map_every qexists_tac [`bactive`,`fd`, `req`, `off`, `buf`] \\ simp[]
    \\ fs[INSTREAM_BUFFERED_FD_def, REF_NUM_def, instream_buffered_inv_def] \\ xsimpl
    \\ fs[PULL_EXISTS] \\  CONV_TAC(RESORT_EXISTS_CONV List.rev)
    \\ map_every qexists_tac [`w`, `r`] \\ xsimpl
    \\ rpt strip_tac
    \\ `MIN req (STRLEN content − pos + (w − r)) = req` by simp[MIN_DEF, NOT_LESS]
    \\ simp[] \\ map_every qexists_tac [`x'`,`x'3'`] \\ simp[]
    \\ simp[TAKE_TAKE_T] \\ `r + req - w = 0` by fs[NOT_LESS]
    \\ simp[TAKE_0]
    \\ `pos + (r + (req + x'³')) − (w + x') = pos` by fs[]
    \\ rw[] \\ simp[MIN_DEF, MAX_DEF]
    \\ simp[fsupdate_unchanged] \\ xsimpl \\ fs []
    \\ `r - w = 0` by fs []
    \\ asm_rewrite_tac [TAKE_0])
  >-(xapp \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
    \\ map_every qexists_tac [`bactive`,`fd`, `req`, `off`, `buf`] \\ simp[]
    \\ fs[INSTREAM_BUFFERED_FD_def, REF_NUM_def, instream_buffered_inv_def] \\ xsimpl
    \\ fs[PULL_EXISTS] \\  CONV_TAC(RESORT_EXISTS_CONV List.rev)
    \\ map_every qexists_tac [`w`, `r`] \\ xsimpl
    \\ rpt strip_tac
    \\ `MIN req (STRLEN content − pos + (w − r)) = req` by simp[MIN_DEF, NOT_LESS]
    \\ simp[] \\ map_every qexists_tac [`x'`,`x'3'`] \\ simp[]
    \\ simp[TAKE_TAKE_T] \\ `r + req - w = 0` by fs[NOT_LESS]
    \\ simp[TAKE_0]
    \\ `pos + (r + (req + x'³')) − (w + x') = pos` by fs[]
    \\ rw[] \\ simp[MIN_DEF, MAX_DEF]
    \\ simp[fsupdate_unchanged] \\ xsimpl \\ fs []
    \\ `r - w = 0` by fs []
    \\ asm_rewrite_tac [TAKE_0])
  \\ xlet `POSTv dc.
         W8ARRAY bufv
          (insert_atI (TAKE (w-r) bactive) off buf) *
         INSTREAM_BUFFERED_BL_FD bcontent (DROP (w-r) bactive) fd is *
         STDIO fs`
   >-(xapp_spec input_aux_w_content_spec \\ xsimpl
      \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
      \\ map_every qexists_tac [`bactive`,`bcontent`,`fd`, `(w-r)`, `off`] \\ xsimpl
      \\ fs[Once INSTREAM_BUFFERED_BL_FD_def, REF_NUM_def, instream_buffered_inv_def] \\ xsimpl
      \\ fs[PULL_EXISTS] \\  CONV_TAC(RESORT_EXISTS_CONV List.rev)
      \\ map_every qexists_tac [`w`, `r`] \\ xsimpl
      \\ rpt strip_tac \\ xsimpl)
  \\ fs[Once INSTREAM_BUFFERED_BL_FD_def, REF_NUM_def, instream_buffered_inv_def]
  \\ xpull
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ simp[]
  \\ xlet_auto_spec (SOME raw_input_spec) >-  xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ qpat_x_assum`is = Conv _ [fdv; rr; wr; buff]` mp_tac
  \\ rveq \\ strip_tac \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rfs[GSYM MIN_DEF]
  \\ qabbrev_tac `take_n = (MIN (MIN (LENGTH bcontent - 4) (LENGTH content - pos))
                              (r + req − w))`
  \\ qabbrev_tac `bactive =  TAKE (w − r) (DROP r bcontent)`
  \\ simp[TAKE_TAKE]
  \\ `0 <= req /\ 0 <= off` by fs[] \\ imp_res_tac INT_OF_NUM_LESS
  \\ imp_res_tac INT_OF_NUM_LE
  \\ `req <= LENGTH bcontent - 4` by fs[INT_OF_NUM_SUBS_2]
  \\ `r + req - w <= LENGTH bcontent - 4` by fs[INT_OF_NUM_SUBS_2]
  \\ xlet `POSTv rv.
         &(NUM take_n rv) *
         W8ARRAY bufv
          (insert_atI
              (TAKE take_n (explode_fromI (LENGTH bcontent - 4)
                   content pos)) (off+w-r)
              (insert_atI bactive off buf)) *
         INSTREAM_BUFFERED_FD
          (DROP take_n (explode_fromI (LENGTH bcontent - 4) content pos)) fd is *
         STDIO (fsupdate fs fd 0 (MIN (LENGTH bcontent - 4 + pos) (MAX pos (LENGTH content)))
     content)`
  >-(xapp \\ xsimpl \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
    \\ rfs[GSYM MIN_DEF]
    \\ map_every qexists_tac
        [`(explode_fromI (LENGTH bcontent - 4) content pos)`, `fd`,
            `take_n`, `off + w − r`]
    \\ xsimpl \\ simp[Abbr`take_n`]
    \\ `(if
           LENGTH bcontent < 4 + (STRLEN content − pos) ∧
           0 < STRLEN content − pos
         then
           LENGTH bcontent − 4
         else (STRLEN content − pos)) =
            MIN (LENGTH bcontent − 4) (STRLEN content − pos)`
        by fs[MIN_DEF]
    \\ `NUM (MIN (MIN (LENGTH bcontent − 4) (STRLEN content − pos))
                    (r + req − w)) nv9` by
     (pop_assum (fn th => full_simp_tac bool_ss [th])
      \\ qpat_x_assum `NUM _ nv9` mp_tac
      \\ qmatch_goalsub_abbrev_tac `k1 < k2:num`
      \\ Cases_on `k1 = k2` \\ fs []
      \\ rewrite_tac [MIN_DEF]
      \\ IF_CASES_TAC \\ simp []
      \\ Cases_on `k1 = STRLEN content − pos` \\ fs []
      \\ qsuff_tac `F` \\ fs []
      \\ pop_assum mp_tac \\ fs [Abbr`k1`,Abbr`k2`]
      \\ simp [MIN_DEF]) \\ fs[]
    \\ simp[Once INSTREAM_BUFFERED_FD_def, REF_NUM_def, instream_buffered_inv_def]
    \\ xsimpl \\ fs[PULL_EXISTS] \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
    \\ qexists_tac `(MIN (LENGTH bcontent − 4) (STRLEN content − pos) + 4)`
    \\ xsimpl \\ simp[LENGTH_explode_fromI, LENGTH_insert_atI, Abbr`bactive`]
    \\ `off +
      (w + MIN (MIN (LENGTH bcontent − 4) (STRLEN content − pos))
              (r + req − w)) ≤ r + LENGTH buf`
          by    (Cases_on `LENGTH bcontent - 4 <= LENGTH content - pos`
                >-(fs[LENGTH_explode_fromI]
                \\ simp[MIN_DEF])
                >-(fs[LENGTH_explode_fromI]
                \\ simp[MIN_DEF])) \\ fs[]
    \\ conj_tac
    >-(disj1_tac
      >-(Cases_on `LENGTH bcontent - 4 <= LENGTH content - pos`
        >-(disj1_tac >- fs[LENGTH_explode_fromI])
        >-(disj2_tac >- fs[LENGTH_explode_fromI])))
    \\ conj_tac
    >-(Cases_on `LENGTH bcontent - 4 <= LENGTH content - pos`
      >-(fs[LENGTH_explode_fromI, LENGTH_insert_atI]
        \\ simp[explode_fromI_def, take_fromI_def]
        \\ simp[insert_atI_def] \\ simp[DROP_LENGTH_TOO_LONG,
        DROP_APPEND] \\ simp[MIN_DEF,TAKE_TAKE_MIN])
      >-(fs[LENGTH_explode_fromI, LENGTH_insert_atI]
        \\ simp[explode_fromI_def, take_fromI_def]
        \\ simp[insert_atI_def] \\ simp[DROP_LENGTH_TOO_LONG, DROP_APPEND]
        \\ simp[MIN_DEF]
        \\ `STRLEN content - pos < LENGTH bcontent - 4` by fs[]
        \\ simp[LENGTH_TAKE_EQ_MIN,LENGTH_TAKE, TAKE_APPEND1, TAKE_TAKE_T,
              TAKE_LENGTH_TOO_LONG]))
    \\ fs[LENGTH_TAKE_EQ_MIN, TAKE_LENGTH_TOO_LONG,DROP_NIL]
    \\ rpt strip_tac \\ simp[MIN_DEF]
    \\ `0 < STRLEN content ==> (0 < pos ∨ 0 < STRLEN content)`
        by (strip_tac \\ disj2_tac \\ fs[])
    \\ `pos = LENGTH content ⇒ MIN (LENGTH bcontent - 4 + pos) (MAX pos (LENGTH content)) = LENGTH content` by simp[MAX_DEF,MIN_DEF]
    \\ simp[MIN_DEF]
    \\ Cases_on `LENGTH content < pos`
    >-(simp[MAX_DEF] \\ xsimpl)
    >-(fs[NOT_LESS]
      \\ `MAX pos (STRLEN content) = STRLEN content` by simp[MAX_DEF]
      \\ simp[] \\ Cases_on `0 < STRLEN content`
      >-xsimpl
      >-xsimpl))
  \\ fs[INSTREAM_BUFFERED_FD_def, REF_NUM_def, instream_buffered_inv_def]
  \\ fs[NUM_def] \\ xpull \\ xapp \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
  \\ fs[NUM_def] \\ asm_exists_tac \\ qexists_tac `&w − &r`
  \\ xsimpl \\ rpt strip_tac \\ map_every qexists_tac [`r''`,`w''`]
  \\ fs[] \\ fs[Abbr`take_n`]
  \\ rename [`INT _ v_6`]
  \\ `INT ((&MIN (STRLEN content − pos)
        (r + req − w)) + (&w − &r)) v_6`
        by (pop_assum mp_tac \\ simp[MIN_DEF])
  \\ `INT (&MIN req (STRLEN content − pos + (w − r))) v_6`
      by  (pop_assum mp_tac
          \\ simp[MIN_DEF]
          \\ CASE_TAC
          >-(simp[INT_OF_NUM_SUBS_2, INT_ADD_CALCULATE, INT_SUB_CALCULATE])
          \\ `r + req - w <= STRLEN content - pos` by
            (pop_assum mp_tac \\ rpt (pop_assum kall_tac) \\ fs [])
          \\ `req <= w + STRLEN content - pos - r` by
            (pop_assum mp_tac
             \\ qpat_x_assum `req ≤ LENGTH bcontent − 4` mp_tac
             \\ qpat_x_assum `r ≤ w` mp_tac
             \\ qpat_x_assum `r + req ≤ _` mp_tac
             \\ qpat_x_assum `4 ≤ r` mp_tac
             \\ qpat_x_assum `w ≤ LENGTH bcontent` mp_tac
             \\ qpat_x_assum `req > w − r` mp_tac
             \\ rpt (pop_assum kall_tac) \\ fs [])
          \\ Cases_on `req = w + STRLEN content − pos − r`
          >-(simp[INT_OF_NUM_SUBS_2, INT_ADD_CALCULATE, INT_SUB_CALCULATE])
          >-(simp[INT_OF_NUM_SUBS_2, INT_ADD_CALCULATE, INT_SUB_CALCULATE]))
  \\ simp[] \\ conj_tac
  >-(simp[explode_fromI_def, take_fromI_def]
    \\ `MIN (MIN (LENGTH bcontent − 4) (STRLEN content − pos)) (r + req − w) =
        MIN (STRLEN content − pos) (r + req − w)` by simp[MIN_DEF]
    \\ simp[] \\ simp[TAKE_TAKE_MIN]
    \\ `MIN (MIN (STRLEN content − pos) (r + req − w)) (LENGTH bcontent − 4) =
         MIN (STRLEN content − pos) (r + req − w)` by simp[MIN_DEF]
    \\ asm_rewrite_tac []
    \\ `LENGTH bactive = w-r` by simp[Abbr`bactive`, LENGTH_TAKE]
    \\ pop_assum mp_tac
    \\ ntac 2 (pop_assum kall_tac)
    \\ simp[insert_atI_insert_atI, Abbr`bactive`]
    \\ simp[MIN_DEF, TAKE_LENGTH_TOO_LONG]
    \\ CASE_TAC
    >-(simp[TAKE_LENGTH_TOO_LONG]))
  \\ qpat_x_assum `r <= w` mp_tac
  \\ qpat_x_assum `r'' <= w''` mp_tac
  \\ qpat_x_assum `req > w-r` mp_tac
  \\ qpat_x_assum `r + req ≤ w + (LENGTH bcontent − 4)` mp_tac
  \\ qpat_x_assum `req ≤ LENGTH bcontent − 4` mp_tac
  \\ qpat_x_assum `1028 <= LENGTH bcontent` mp_tac
  \\ qpat_x_assum ` _ = w'' - r''` mp_tac
  \\ rpt (pop_assum kall_tac) \\ rpt strip_tac
  \\ Cases_on `LENGTH bcontent - 4 <= LENGTH content - pos`
  >-(Cases_on `LENGTH content - pos <= req`
    >-(`LENGTH bcontent - 4 = req - (w-r) + (w''-r'')`
            by (qpat_x_assum ` _ = w'' - r''` mp_tac
                \\ simp[MIN_DEF, LENGTH_explode_fromI])
      \\ qpat_x_assum ` _ = w'' - r''` kall_tac
      \\ `LENGTH bcontent − 4 = (r + (req + w'')) − (r'' + w)`
        by simp[]
      \\ `pos + (LENGTH bcontent − 4) = pos + (r + (req + w'') − (r'' + w))`
          by simp[]
      \\ `(MIN (pos + (r + (req + w'')) − (r'' + w)) (MAX pos (STRLEN content))) =
        (MIN (pos + LENGTH bcontent − 4) (MAX pos (STRLEN content)))` by simp[MIN_DEF]
      \\ rw[] \\ xsimpl)
    >-(`LENGTH bcontent - 4 = req - (w-r) + (w''-r'')`
            by (qpat_x_assum ` _ = w'' - r''` mp_tac
                \\ simp[MIN_DEF, LENGTH_explode_fromI])
      \\ qpat_x_assum ` _ = w'' - r''` kall_tac
      \\ `LENGTH bcontent − 4 = (r + (req + w'')) − (r'' + w)`
        by simp[]
      \\ `pos + (LENGTH bcontent − 4) = pos + (r + (req + w'') − (r'' + w))`
          by simp[]
      \\ `(MIN (pos + (r + (req + w'')) − (r'' + w)) (MAX pos (STRLEN content))) =
        (MIN (pos + LENGTH bcontent − 4) (MAX pos (STRLEN content)))` by simp[MIN_DEF]
      \\ rw[] \\ xsimpl))
  >-(Cases_on `LENGTH content - pos < req - (w - r)`
    >-(qpat_x_assum ` _ = w'' - r''` mp_tac
      \\ simp[MIN_DEF, MAX_DEF, LENGTH_explode_fromI]
      \\ strip_tac \\ xsimpl)
  >-(qpat_x_assum ` _ = w'' - r''` mp_tac
      \\ simp[MIN_DEF, MAX_DEF, LENGTH_explode_fromI]
      \\ strip_tac \\ xsimpl))
QED

Theorem print_list_spec:
   ∀ls lv fs out. LIST_TYPE STRING_TYPE ls lv ⇒
   app (p:'ffi ffi_proj) TextIO_print_list_v [lv]
     (STDIO fs)
     (POSTv v. &UNIT_TYPE () v * STDIO (add_stdout fs (concat ls)))
Proof
  Induct \\ rw[LIST_TYPE_def]
  \\ xcf_with_def TextIO_print_list_v_def
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
  \\ xsimpl
QED

(* a layer that makes buffered I/O nicer to work with *)

Definition INSTREAM_STR_def:
  INSTREAM_STR fd is (str:string) fs =
    SEP_EXISTS read active left.
      INSTREAM_BUFFERED_FD (MAP (n2w o ORD) active) fd is *
      & (str = active ++ left /\
         get_file_content fs fd = SOME(read ++ str, LENGTH read + LENGTH active) /\
         get_mode fs fd = SOME ReadMode)
End

Theorem INSTREAM_STR_fd_neq:
  STD_streams fs ⇒
  INSTREAM_STR fd is s fs =
  INSTREAM_STR fd is s fs * &(fd ≠ 1 ∧ fd ≠ 2)
Proof
  strip_tac
  \\ drule_then assume_tac STD_streams_get_mode
  \\ Cases_on ‘fd ≠ 1 ∧ fd ≠ 2’
  \\ gvs [INSTREAM_STR_def, SEP_CLAUSES]
QED

Theorem INSTREAM_STR_add_stdout:
  STD_streams fs ⇒
  INSTREAM_STR fd is rest (add_stdout fs s) =
  INSTREAM_STR fd is rest fs
Proof
  simp [FUN_EQ_THM] \\ rpt strip_tac
  \\ drule STD_streams_add_stdout
  \\ disch_then $ qspec_then ‘s’ assume_tac
  \\ imp_res_tac INSTREAM_STR_fd_neq
  \\ ntac 2 $ pop_assum $ once_rewrite_tac o sing
  \\ iff_tac
  \\ simp [STAR_def, cond_def] \\ rpt strip_tac \\ instantiate
  \\ qpat_x_assum ‘INSTREAM_STR _ _ _ _ _’ mp_tac
  \\ simp [INSTREAM_STR_def]
  \\ DEP_REWRITE_TAC [get_file_content_add_stdout]
  \\ simp []
QED

(* Useful for applying fastForwardFD_forwardFD *)
Theorem INSTREAM_STR_get_file_content:
  INSTREAM_STR fd is s (forwardFD fs fd k) =
  INSTREAM_STR fd is s (forwardFD fs fd k) *
  &(∃content pos.
      get_file_content fs fd = SOME (content,pos) ∧ pos + k ≤ STRLEN content)
Proof
  qmatch_goalsub_abbrev_tac ‘&P’
  \\ Cases_on ‘P’ \\ gvs [SEP_CLAUSES]
  \\ simp [FUN_EQ_THM, SEP_F_def]
  \\ rpt strip_tac
  \\ gvs [INSTREAM_STR_def, SEP_EXISTS_THM, STAR_def, cond_def]
QED

Definition INSTREAM_STR'_def:
  INSTREAM_STR' fd is (str:string) fs non_empty is_empty =
    SEP_EXISTS read active left.
      INSTREAM_BUFFERED_FD (MAP (n2w o ORD) active) fd is *
      & (str = active ++ left /\
         (non_empty ⇒ active ≠ []) ∧ (is_empty ⇒ active = []) ∧
         get_file_content fs fd = SOME(read ++ str, LENGTH read + LENGTH active) /\
         get_mode fs fd = SOME ReadMode)
End

Theorem INSTREAM_STR'_F_F[local]:
  INSTREAM_STR' fd is input fs F F = INSTREAM_STR fd is input fs
Proof
  gvs [INSTREAM_STR'_def,INSTREAM_STR_def]
QED

Definition splitlines_at_def:
  splitlines_at c0 ls =
    (let
       lines = FIELDS ($= c0) ls
     in
       if NULL (LAST lines) then FRONT lines else lines)
End

Definition lines_of_gen_def:
  lines_of_gen c0 s =
    MAP (λx. implode x ^ (str c0)) (splitlines_at c0 (explode s))
End

(* TODO Maybe splitlines should be defined exactly like this. *)
Theorem splitlines_at_splitlines:
  splitlines_at #"\n" s = splitlines s
Proof
  simp [splitlines_at_def, splitlines_def]
QED

(* TODO Maybe lines_of should be defined exactly like this. *)
Theorem lines_of_gen_lines_of:
  lines_of_gen #"\n" s = lines_of s
Proof
  simp [lines_of_gen_def, lines_of_def, splitlines_at_splitlines, str_def]
QED

Definition INSTREAM_LINES_def:
  INSTREAM_LINES c0 fd is (lines:mlstring list) fs =
    SEP_EXISTS rest.
      INSTREAM_STR fd is rest fs *
      & (lines_of_gen c0 (implode rest) = lines)
End

(* Useful for applying fastForwardFD_forwardFD *)
Theorem INSTREAM_LINES_get_file_content:
  INSTREAM_LINES c0 fd is lines (forwardFD fs fd k) =
  INSTREAM_LINES c0 fd is lines (forwardFD fs fd k) *
  &(∃content pos.
      get_file_content fs fd = SOME (content,pos) ∧ pos + k ≤ STRLEN content)
Proof
  simp [INSTREAM_LINES_def, Once INSTREAM_STR_get_file_content]
  \\ simp [FUN_EQ_THM, SEP_EXISTS_THM, cond_def, STAR_def]
  \\ metis_tac []
QED

Theorem INSTREAM_LINES_fd_neq:
  STD_streams fs ⇒
  INSTREAM_LINES c0 fd is s fs =
  INSTREAM_LINES c0 fd is s fs * &(fd ≠ 1 ∧ fd ≠ 2)
Proof
  strip_tac
  \\ drule_then assume_tac STD_streams_get_mode
  \\ Cases_on ‘fd ≠ 1 ∧ fd ≠ 2’
  \\ gvs [INSTREAM_LINES_def, INSTREAM_STR_def, SEP_CLAUSES]
QED

Theorem INSTREAM_LINES_add_stdout:
  STD_streams fs ⇒
  INSTREAM_LINES c0 fd is rest (add_stdout fs s) =
  INSTREAM_LINES c0 fd is rest fs
Proof
  simp [INSTREAM_LINES_def, Once INSTREAM_STR_add_stdout]
QED

(* TODO: COPIED THEOREMS ABOUT splitlines *)
Theorem splitlines_at_next:
   splitlines_at c0 ls = ln::lns ⇒
   splitlines_at c0 (DROP (SUC (LENGTH ln)) ls) = lns ∧
   ln ≼ ls ∧ (LENGTH ln < LENGTH ls ⇒ ln ++ [c0] ≼ ls)
Proof
  simp[splitlines_at_def]
  \\ Cases_on`FIELDS ($= c0) ls` \\ fs[]
  \\ Cases_on`LENGTH h < LENGTH ls`
  >- (
    imp_res_tac FIELDS_next
    \\ strip_tac
    \\ `ln = h`
    by (
      pop_assum mp_tac \\ rw[]
      \\ fs[FRONT_DEF] )
    \\ fs[]
    \\ fs[LAST_DEF,NULL_EQ]
    \\ Cases_on`t = []` \\ fs[]
    \\ fs[FRONT_DEF]
    \\ IF_CASES_TAC \\ fs[]
    \\ fs[IS_PREFIX_APPEND])
  \\ fs[NOT_LESS]
  \\ imp_res_tac FIELDS_full \\ fs[]
  \\ IF_CASES_TAC \\ fs[]
  \\ strip_tac \\ rveq \\ fs[]
  \\ simp[DROP_LENGTH_TOO_LONG,FIELDS_def]
QED

Theorem splitlines_at_nil[simp] = EVAL“splitlines_at c0 ""”

Theorem splitlines_at_eq_nil[simp]:
   splitlines_at c0 ls = [] ⇔ (ls = [])
Proof
  rw[EQ_IMP_THM]
  \\ fs[splitlines_at_def]
  \\ every_case_tac \\ fs[]
  \\ Cases_on`FIELDS ($= c0) ls` \\ fs[]
  \\ fs[LAST_DEF] \\ rfs[NULL_EQ]
  \\ Cases_on`LENGTH "" < LENGTH ls`
  >- ( imp_res_tac FIELDS_next \\ fs[] )
  \\ fs[LENGTH_NIL]
QED

Theorem lines_of_gen_nil[simp]:
  lines_of_gen c0 s = [] ⇔ s = «»
Proof
  simp [lines_of_gen_def, explode_eq]
QED

Theorem splitlines_at_CONS_FST_SPLITP:
   splitlines_at c0 ls = ln::lns ⇒ FST (SPLITP ($= c0) ls) = ln
Proof
  rw[splitlines_at_def]
  \\ Cases_on`ls` \\ fs[FIELDS_def]
  \\ TRY pairarg_tac \\ fs[] \\ rw[] \\ fs[]
  \\ every_case_tac \\ fs[] \\ rw[] \\ fs[NULL_EQ, FIELDS_def]
  \\ qmatch_assum_abbrev_tac`FRONT (x::y) = _`
  \\ Cases_on`y` \\ fs[]
QED

Theorem splitlines_at_not_exists2:
  !l.
        ~(EXISTS ($= c0) l) ==>
        splitlines_at c0 l = if l = "" then [] else [l]
Proof
  rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l` >- fs[]
  \\ `h <> c0` by fs[EVERY_DEF]
  \\ fs[splitlines_at_def, FRONT_DEF, FIELDS_def, SPLITP, NULL_DEF]
  \\ CASE_TAC
  >-(CASE_TAC
    >-(fs[FRONT_DEF])
    >-(`SPLITP ($= c0) t = (t, [])`  by metis_tac[NOT_DEF,SPLITP_EVERY]
      \\ fs[FST]))
  >-(CASE_TAC
    >-(fs[FRONT_DEF]
      \\ `SPLITP ($= c0) t = (t, [])`  by metis_tac[NOT_DEF,SPLITP_EVERY]
      \\ fs[FST])
    >-(`SPLITP ($= c0) t = (t, [])`  by metis_tac[NOT_DEF,SPLITP_EVERY]
      \\ fs[FST]))
QED

Theorem FIELDS_hd_c0:
  !t.
        FIELDS ($= c0) (STRING c0 t) = "":: FIELDS ($= c0) t
Proof
  rpt strip_tac
  \\ fs[FIELDS_def, SPLITP]
QED

Theorem SPLITP_takeUntil_c0:
  !l.
        SPLITP ($= c0) l =
          (takeUntil ($= c0) l, DROP (LENGTH (takeUntil ($= c0) l)) l)
Proof
  completeInduct_on `LENGTH l`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[SPLITP, mllistTheory.takeUntil_def])
  >-(Cases_on `h = c0`
    >-fs[SPLITP, mllistTheory.takeUntil_def]
    >-(fs[SPLITP, mllistTheory.takeUntil_def]))
QED

Theorem FIELDS_takeUntil_c0:
  !l.
      LENGTH (takeUntil ($= c0) l) < LENGTH l ==>
      FIELDS ($= c0) l =
          takeUntil ($= c0) l ::
            FIELDS ($= c0) (TL (DROP (LENGTH (takeUntil ($= c0) l)) l))
Proof
  completeInduct_on `LENGTH (l:string)`
  \\ rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ Cases_on `l`
  >-(fs[mllistTheory.takeUntil_def])
  >-(Cases_on `h = c0`
    >-(simp[mllistTheory.takeUntil_def]
      \\ fs[FIELDS_hd_c0])
    >-(fs[FIELDS_def, SPLITP_takeUntil_c0]
      \\ `~(NULL (takeUntil ($= c0) (STRING h t)))` by fs[mllistTheory.takeUntil_def, NULL_DEF]
      \\ simp[] \\ Cases_on `LENGTH (takeUntil ($= c0) (STRING h t)) = LENGTH (STRING h t)`
      >-(fs[DROP_LENGTH_TOO_LONG])
      \\ `STRLEN (takeUntil ($= c0) (STRING h t)) < STRLEN (STRING h t)` by fs[LENGTH_CONS]
      \\ `(DROP (STRLEN (takeUntil ($= c0) (STRING h t))) (STRING h t)) <> []` by fs[DROP_NIL]
      \\ Cases_on `DROP (STRLEN (takeUntil ($= c0) (STRING h t))) (STRING h t)`
      >- fs[]
      \\ `~(NULL (STRING h' t'))` by fs[NULL_DEF]
      \\ simp[]))
QED

Theorem splitlines_at_hd_c0:
  !t.
        splitlines_at c0 (STRING c0 t) = "" :: splitlines_at c0 t
Proof
  rpt strip_tac \\ fs[splitlines_at_def]
  \\ CASE_TAC
  >-(CASE_TAC
    >-(fs[FRONT_DEF, FIELDS_hd_c0])
    >-(fs[NULL_DEF,LAST_DEF, FIELDS_hd_c0]))
  >-(CASE_TAC
    >-(fs[NULL_DEF, LAST_DEF, FIELDS_hd_c0])
    >-(fs[FIELDS_hd_c0]))
QED

Theorem splitlines_at_takeUntil_exists:
  !l.
        EXISTS ($= c0) l ==>
        splitlines_at c0 l =
          (takeUntil ($= c0) l ::
            splitlines_at c0 (TL (DROP (LENGTH (takeUntil ($= c0) l)) l)))
Proof
  rpt strip_tac \\ rveq \\ fs [PULL_FORALL]
  \\ `LENGTH (takeUntil ($= c0) l) < LENGTH l` by fs[LENGTH_takeUntil_exists]
  \\ Cases_on `l`
  >-(fs[splitlines_at_eq_nil, mllistTheory.takeUntil_def])
  >-(Cases_on `h = c0`
    >-(fs[mllistTheory.takeUntil_def, splitlines_at_hd_c0])
    >-(simp[mllistTheory.takeUntil_def, splitlines_at_def]
      \\ `~(NULL (takeUntil ($= c0) (STRING h t)))` by fs[mllistTheory.takeUntil_def, NULL_DEF]
      \\ CASE_TAC
      >-(CASE_TAC
        >-(fs[FIELDS_takeUntil_c0, FRONT_DEF, FIELDS_NEQ_NIL, mllistTheory.takeUntil_def])
        >-(`LENGTH (takeUntil ($= c0) (STRING h t)) < LENGTH (STRING h t)` by fs[LENGTH_takeUntil_exists]
          \\ cases_on `c0 = h` >- fs[]
          \\ ` FIELDS ($= c0) (STRING h t) =
                takeUntil ($= c0) (STRING h t)::
             FIELDS ($= c0)
               (TL (DROP (STRLEN (takeUntil ($= c0) (STRING h t))) (STRING h t)))` by fs[FIELDS_takeUntil_c0]
          \\ fs[mllistTheory.takeUntil_def, LAST_DEF]))
      >-(cases_on `c0 = h` >- fs[]
        \\ `FIELDS ($= c0) (STRING h t) =
                takeUntil ($= c0) (STRING h t)::
             FIELDS ($= c0)
               (TL (DROP (STRLEN (takeUntil ($= c0) (STRING h t))) (STRING h t)))` by fs[FIELDS_takeUntil_c0]
        \\ fs[FIELDS_takeUntil_c0, mllistTheory.takeUntil_def] \\ rfs[]
        \\ fs[LAST_DEF])))
QED

Theorem splitlines_at_takeUntil_exists2:
  !l.
        EXISTS ($= c0) l ==>
        splitlines_at c0 l =
          (takeUntil ($= c0) l ::
            splitlines_at c0 (DROP (SUC (LENGTH (takeUntil ($= c0) l))) l))
Proof
  rpt strip_tac
  \\ imp_res_tac splitlines_at_takeUntil_exists
  \\ `DROP (SUC (STRLEN (takeUntil ($= c0) l))) l =
      DROP 1 (DROP (STRLEN (takeUntil ($= c0) l)) l)` by fs[SUC_ONE_ADD, DROP_DROP_T]
  \\ rw[] \\ cases_on `DROP (STRLEN (takeUntil ($= c0) l)) l`
  >-fs[takeUntilIncl_length_gt_0] >-fs[TL, DROP]
QED

(*** END TODO COPIED ***)

Theorem MAP_MAP_n2w_ORD[local]:
  (!xs. MAP (n2w ∘ ORD) (MAP (CHR ∘ (w2n:word8 -> num)) xs) = xs) /\
  (!xs. MAP (CHR ∘ (w2n:word8 -> num)) (MAP (n2w ∘ ORD) xs) = xs)
Proof
  conj_tac \\ Induct \\ fs []
QED

Theorem input1_spec_str:
  app (p:'ffi ffi_proj) TextIO_input1_v [is]
     (STDIO fs * INSTREAM_STR fd is s fs)
     (POSTv chv.
       SEP_EXISTS k.
         STDIO (forwardFD fs fd k) *
         INSTREAM_STR fd is (TL s) (forwardFD fs fd k) *
         & (OPTION_TYPE CHAR (oHD s) chv))
Proof
  simp_tac bool_ss [INSTREAM_STR_def,SEP_CLAUSES]
  \\ xpull
  \\ match_mp_tac (MP_CANON app_wgframe)
  \\ mp_tac (GEN_ALL input1_spec) \\ fs []
  \\ rpt (disch_then drule)
  \\ disch_then (qspecl_then [`p`,`is`,`MAP (n2w ∘ ORD) active`] mp_tac)
  \\ strip_tac \\ asm_exists_tac \\ fs []
  \\ rfs [] \\ pop_assum kall_tac
  \\ reverse (Cases_on `active`) \\ fs []
  THEN1
   (xsimpl \\ fs [] \\ rw []
    \\ qexists_tac `0`
    \\ qexists_tac `t`
    \\ qexists_tac `left`
    \\ fs [ADD1]
    \\ xsimpl)
  \\ TOP_CASE_TAC
  THEN1
   (fs [] \\ Cases_on `s` \\ rveq \\ fs []
    \\ xsimpl \\ fs [] \\ rw [] \\ xsimpl)
  \\ xsimpl \\ rveq \\ fs []
  \\ Cases_on `left` \\ fs [EL_LENGTH_APPEND]
  \\ fs [ADD1] \\ rw []
  \\ fs [explode_fromI_def,take_fromI_def]
  \\ ntac 2 (pop_assum mp_tac)
  \\ qmatch_goalsub_abbrev_tac `DROP k (xs ++ ys)`
  \\ `k = LENGTH xs` by fs [Abbr`k`,Abbr`xs`]
  \\ fs [rich_listTheory.DROP_LENGTH_APPEND]
  \\ rw []
  \\ qexists_tac `LENGTH x + 1`
  \\ qexists_tac `MAP (CHR o w2n) x`
  \\ qexists_tac `DROP (LENGTH x) t`
  \\ fs [MAP_MAP_n2w_ORD]
  \\ xsimpl
  \\ qmatch_goalsub_abbrev_tac `STRCAT zs _`
  \\ qsuff_tac `zs = TAKE (LENGTH x) t` THEN1 simp [TAKE_DROP]
  \\ fs [Abbr`zs`]
  \\ qpat_x_assum `x = _` (fn th => CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [th])))
  \\ fs [MAP_TAKE] \\ fs [Abbr`ys`,MAP_MAP_n2w_ORD]
QED

Theorem peekChar_spec_str:
  app (p:'ffi ffi_proj) TextIO_peekChar_v [is]
     (STDIO fs * INSTREAM_STR fd is s fs)
     (POSTv chv.
       SEP_EXISTS k.
         STDIO (forwardFD fs fd k) *
         INSTREAM_STR fd is s (forwardFD fs fd k) *
         & (OPTION_TYPE CHAR (oHD s) chv))
Proof
  simp_tac bool_ss [INSTREAM_STR_def,SEP_CLAUSES]
  \\ xpull
  \\ match_mp_tac (MP_CANON app_wgframe)
  \\ mp_tac (GEN_ALL peekChar_spec) \\ fs []
  \\ rpt (disch_then drule)
  \\ disch_then (qspecl_then [`p`,`is`,`MAP (n2w ∘ ORD) active`] mp_tac)
  \\ strip_tac \\ asm_exists_tac \\ fs []
  \\ rfs [] \\ pop_assum kall_tac
  \\ reverse (Cases_on `active`) \\ fs []
  THEN1
   (xsimpl \\ fs [] \\ rw []
    \\ qexists_tac `0`
    \\ qexists_tac `h::t`
    \\ qexists_tac `left`
    \\ fs [ADD1]
    \\ xsimpl)
  \\ TOP_CASE_TAC
  THEN1
   (fs [] \\ Cases_on `s` \\ rveq \\ fs []
    \\ xsimpl \\ fs [] \\ rw [] \\ xsimpl)
  \\ xsimpl \\ rveq \\ fs []
  \\ rw []
  \\ qexists_tac `MAP (CHR o w2n) x`
  \\ qexists_tac `DROP (LENGTH x) left`
  \\ fs []
  \\ fs [MAP_MAP_n2w_ORD] \\ xsimpl
  \\ reverse conj_tac
  >- (Cases_on `left` \\ fs [EL_LENGTH_APPEND])
  \\ fs [explode_fromI_def,take_fromI_def]
  \\ qabbrev_tac ‘k = LENGTH x’
  \\ fs [MAP_TAKE,MAP_DROP]
  \\ fs [MAP_MAP_n2w_ORD,rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem peekChar_spec_lines:
  app (p:'ffi ffi_proj) TextIO_peekChar_v [is]
     (STDIO fs * INSTREAM_LINES c0 fd is s fs)
     (POSTv chv.
       SEP_EXISTS k.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES c0 fd is s (forwardFD fs fd k) *
         & (OPTION_TYPE CHAR (case s of [] => NONE | (l::ls) => oHD (explode l ++ [c0])) chv))
Proof
  simp_tac bool_ss [INSTREAM_LINES_def,SEP_CLAUSES]
  \\ xpull
  \\ xapp_spec peekChar_spec_str
  \\ qexists_tac ‘emp’
  \\ xsimpl
  \\ qexists_tac ‘rest’
  \\ qexists_tac ‘fs’
  \\ qexists_tac ‘fd’
  \\ xsimpl
  \\ rw []
  \\ qexists_tac ‘x’
  \\ qexists_tac ‘rest’
  \\ xsimpl
  \\ fs [lines_of_gen_def]
  \\ pop_assum mp_tac
  \\ match_mp_tac (METIS_PROVE [] “x = y ⇒ f x z ⇒ f y z”)
  \\ Cases_on ‘¬EXISTS ($= c0) rest’
  >- (
    drule splitlines_at_not_exists2 \\ fs []
    \\ Cases_on ‘rest’ \\ fs [])
  \\ fs []
  \\ drule splitlines_at_takeUntil_exists
  \\ rw []
  \\ Cases_on ‘rest’ \\ fs [] \\ gvs []
  \\ EVAL_TAC
  \\ IF_CASES_TAC \\ gvs []
  \\ IF_CASES_TAC \\ gvs []
  \\ gvs[ORD_11]
QED

Definition file_content_def:
  file_content fs fname =
    case ALOOKUP fs.files fname of
    | NONE => NONE
    | SOME ino => ALOOKUP fs.inode_tbl (File ino)
End

Definition stdin_content_def:
  stdin_content fs =
    if ALOOKUP fs.infds 0 = SOME (UStream(strlit "stdin"),ReadMode,0) then
      SOME (THE (ALOOKUP fs.inode_tbl (UStream(strlit "stdin"))))
    else NONE
End

Theorem openStdIn_spec_str:
  stdin_content fs = SOME text ∧
  UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) TextIO_openStdIn_v [uv]
     (STDIO fs)
     (POSTv is. STDIO fs * INSTREAM_STR 0 is text fs)
Proof
  rw[stdin_content_def,AllCaseEqs()]
  \\ reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull )
  \\ reverse(Cases_on`∃ll. wfFS (fs with numchars := ll)`) >- (fs[STDIO_def,IOFS_def] \\ xpull)
  \\ `∃cnt. get_file_content fs 0 = SOME (cnt,0)`
      by (simp[get_file_content_def, PULL_EXISTS]
          \\ fs[STD_streams_def]
          \\ last_x_assum(qspecl_then[`0`,`ReadMode`,`inp`]mp_tac)
          \\ simp[] \\ strip_tac
          \\ fs[wfFS_def]
          \\ imp_res_tac ALOOKUP_MEM
          \\ first_x_assum(qspec_then`0`mp_tac)
          \\ simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD]
          \\ disch_then drule \\ strip_tac
          \\ qmatch_goalsub_abbrev_tac`ALOOKUP aa bb = SOME _`
          \\ Cases_on`ALOOKUP aa bb` \\ fs[Abbr`aa`,Abbr`bb`]
          \\ imp_res_tac ALOOKUP_FAILS \\ fs[])
  \\ rw [INSTREAM_STR_def,SEP_CLAUSES]
  \\ match_mp_tac (MP_CANON app_wgframe)
  \\ mp_tac (GEN_ALL openStdIn_STDIO_spec)
  \\ disch_then drule
  \\ disch_then (qspecl_then [‘p’,‘fs’] assume_tac)
  \\ asm_exists_tac
  \\ xsimpl
  \\ gvs [get_file_content_def,AllCaseEqs(),get_mode_def]
QED

Theorem openIn_spec_str:
  FILENAME s sv /\ hasFreeFD fs /\ file_content fs s = SOME text ==>
  app (p:'ffi ffi_proj) TextIO_openIn_v [sv]
     (STDIO fs)
     (POSTv is.
        STDIO (openFileFS s fs ReadMode 0) *
        INSTREAM_STR (nextFD fs) is text (openFileFS s fs ReadMode 0))
Proof
  rw [INSTREAM_STR_def,SEP_CLAUSES]
  \\ match_mp_tac (MP_CANON app_wgframe)
  \\ mp_tac (GEN_ALL openIn_STDIO_spec)
  \\ rpt (disch_then drule) \\ fs []
  \\ rpt (disch_then drule)
  \\ `inFS_fname fs s` by fs [inFS_fname_def,file_content_def,CaseEq"option"]
  \\ disch_then (qspec_then `p` mp_tac)
  \\ strip_tac \\ asm_exists_tac \\ asm_rewrite_tac []
  \\ xsimpl
  \\ fs [] \\ rw []
  \\ qexists_tac `[]`
  \\ qexists_tac `[]`
  \\ qexists_tac `THE (file_content fs s)`
  \\ xsimpl
  \\ imp_res_tac nextFD_ltX
  \\ fs [inFS_fname_def,file_content_def,CaseEq"option",openFileFS_def,openFile_def]
  \\ fs [get_file_content_def,get_mode_def]
QED

Theorem closeIn_spec_str:
   fd >= 3 /\ fd <= fs.maxFD ⇒
   app (p:'ffi ffi_proj) TextIO_closeIn_v [is]
     (STDIO fs * INSTREAM_STR fd is text fs)
     (POSTve
        (\u. &(UNIT_TYPE () u /\ validFileFD fd fs.infds) *
             STDIO (fs with infds updated_by ADELKEY fd))
        (\e. &(InvalidFD_exn e /\ ¬ validFileFD fd fs.infds) * STDIO fs))
Proof
  rw [INSTREAM_STR_def,SEP_CLAUSES] \\ xpull
  \\ match_mp_tac (MP_CANON app_wgframe)
  \\ mp_tac (GEN_ALL closeIn_STDIO_spec)
  \\ disch_then drule
  \\ disch_then drule
  \\ disch_then (qspecl_then [`p`,`is`,`MAP (n2w ∘ ORD) active`] mp_tac)
  \\ strip_tac \\ asm_exists_tac \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ xsimpl
QED

Theorem str_STRING:
  str h = implode (STRING h "")
Proof
  EVAL_TAC
QED

Theorem TOKENS_EQ_SING:
  EVERY ($~ o f) xs ∧ xs ≠ [] ⇒ TOKENS f xs = [xs]
Proof
  strip_tac
  \\ ‘SPLITP f xs = (xs,[])’ by
      (match_mp_tac rich_listTheory.SPLITP_EVERY \\ fs [EVERY_MEM])
  \\ Cases_on ‘xs’ \\ fs [TOKENS_def] \\ fs [UNCURRY]
QED

Theorem TOKENS_CONS:
  f x ⇒ TOKENS f (x::xs) = TOKENS f xs
Proof
  fs [TOKENS_def,UNCURRY,SPLITP]
QED

Theorem openStdIn_spec_lines:
  stdin_content fs = SOME text ∧
  UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) TextIO_openStdIn_v [uv]
     (STDIO fs)
     (POSTv is. STDIO fs * INSTREAM_LINES c0 0 is (lines_of_gen c0 (implode text)) fs)
Proof
  rw [INSTREAM_LINES_def,SEP_CLAUSES]
  \\ xapp_spec openStdIn_spec_str
  \\ qexists_tac ‘emp’
  \\ first_x_assum $ irule_at (Pos hd)
  \\ xsimpl \\ rw []
  \\ qexists_tac ‘text’ \\ fs [implode_def]
  \\ xsimpl
QED

(* TODO: copied from fsFFIProps *)
Overload all_lines_inode_gen =
  ``λc0 fs ino. lines_of_gen c0 (implode (THE (ALOOKUP fs.inode_tbl ino)))``

Definition all_lines_file_gen_def:
  all_lines_file_gen c0 fs fname =
    all_lines_inode_gen c0 fs (File (THE(ALOOKUP fs.files fname)))
End

(* end TODO: copied from fsFFIProps *)

Theorem all_lines_file_gen_all_lines_file[simp]:
  all_lines_file_gen #"\n" fs f =
  all_lines_file fs f
Proof
  rw[all_lines_file_def,all_lines_file_gen_def,lines_of_def,lines_of_gen_def,
     splitlines_at_def,splitlines_def,str_def]
QED

(* TODO Move to fsFFIProps? *)
Theorem all_lines_file_gen_lines_of_gen:
  file_content fs fname = SOME s ⇒
  all_lines_file_gen c0 fs fname = lines_of_gen c0 (implode s)
Proof
  simp [file_content_def, AllCaseEqs()]
  \\ rpt strip_tac
  \\ simp [all_lines_file_gen_def, lines_of_gen_def]
QED

Theorem openIn_spec_lines:
  FILENAME s sv /\ hasFreeFD fs /\ inFS_fname fs s ==>
  app (p:'ffi ffi_proj) TextIO_openIn_v [sv]
     (STDIO fs)
     (POSTv is.
        STDIO (openFileFS s fs ReadMode 0) *
        INSTREAM_LINES c0 (nextFD fs) is (all_lines_file_gen c0 fs s)
          (openFileFS s fs ReadMode 0))
Proof
  reverse (Cases_on `consistentFS fs`) THEN1
   (fs [STDIO_def,IOFS_def,wfFS_def] \\ rw [] \\ xpull
    \\ fs [consistentFS_def] \\ metis_tac [])
  \\ rw [INSTREAM_LINES_def,SEP_CLAUSES]
  \\ match_mp_tac (MP_CANON app_wgframe)
  \\ mp_tac (GEN_ALL openIn_spec_str)
  \\ rpt (disch_then drule) \\ fs []
  \\ rpt (disch_then drule)
  \\ fs [all_lines_file_gen_def,file_content_def]
  \\ drule fsFFIPropsTheory.inFS_fname_ALOOKUP_EXISTS
  \\ disch_then drule \\ strip_tac \\ fs []
  \\ rename [`_ = SOME content`]
  \\ disch_then (qspec_then `p` mp_tac)
  \\ strip_tac \\ asm_exists_tac \\ asm_rewrite_tac []
  \\ xsimpl
  \\ fs [] \\ rw []
  \\ qexists_tac `content`
  \\ xsimpl \\ fs []
QED

Theorem closeIn_spec_lines:
   fd >= 3 /\ fd <= fs.maxFD ⇒
   app (p:'ffi ffi_proj) TextIO_closeIn_v [is]
     (STDIO fs * INSTREAM_LINES c0 fd is lines fs)
     (POSTve
        (\u. &(UNIT_TYPE () u /\ validFileFD fd fs.infds) *
             STDIO (fs with infds updated_by ADELKEY fd))
        (\e. &(InvalidFD_exn e /\ ¬ validFileFD fd fs.infds) * STDIO fs))
Proof
  rw [INSTREAM_LINES_def,SEP_CLAUSES] \\ xpull
  \\ match_mp_tac (MP_CANON app_wgframe)
  \\ mp_tac (GEN_ALL closeIn_spec_str)
  \\ disch_then drule
  \\ disch_then drule
  \\ disch_then (qspecl_then [`rest`,`p`,`is`] mp_tac)
  \\ strip_tac \\ asm_exists_tac \\ asm_rewrite_tac [] \\ pop_assum kall_tac
  \\ xsimpl
QED

Theorem split_exists[local]:
  !input.
    ?to_read text.
      input = to_read ++ text /\
      ((text ≠ "" ⇒ HD text = c0) ∧ EVERY (λc. c ≠ c0) to_read)
Proof
  Induct \\ fs [] \\ rveq \\ fs [] \\ rw []
  \\ Cases_on ‘h = c0’ \\ fs [] \\ rveq \\ fs []
  THEN1 (qexists_tac ‘""’ \\ fs [])
  \\ qexists_tac ‘h::to_read’
  \\ qexists_tac ‘text’ \\ fs []
QED

Theorem fastForwardFD_eq_forwardFD[local]:
∀fs fd c off x.
  get_file_content fs fd = SOME (c,off)
  ∧ STRLEN c = off + x
  ⇒ forwardFD fs fd x = fastForwardFD fs fd
Proof
  rw[forwardFD_def,fastForwardFD_def,get_file_content_def]
  \\ PairCases_on ‘x'’
  \\ qmatch_assum_rename_tac ‘ALOOKUP _ _ = SOME (ino,mode,off')’
  \\ gs[] \\ simp[miscTheory.the_def,AFUPDKEY_ALOOKUP,MAX_DEF]
  \\ simp[IO_fs_component_equality] \\ irule AFUPDKEY_eq
  \\ rw[] \\ simp[MAX_DEF]
QED

Theorem fastForwardFD_same_infds[local]:
  ∀fs n. MAP FST (fastForwardFD fs n).infds = MAP FST fs.infds
Proof
  rw[fastForwardFD_def]
  \\ Cases_on ‘ALOOKUP fs.infds n’
  \\ simp[miscTheory.the_def]
  \\ PairCases_on ‘x’ \\ simp[]
  \\ Cases_on ‘ALOOKUP fs.inode_tbl x0’
  \\ simp[miscTheory.the_def]
QED

Theorem INSTREAM_STR_fastForwardFD:
  STDIO (forwardFD fs fd x) * INSTREAM_STR fd is "" (forwardFD fs fd x) ==>>
  STDIO (fastForwardFD fs fd) * INSTREAM_STR fd is "" (fastForwardFD fs fd) * GC
Proof
  rw [INSTREAM_STR_def]
  \\ xsimpl \\ rw[] \\ gs[] \\ rveq
  \\ qmatch_assum_rename_tac ‘get_file_content _ _ = SOME (c,off)’
  \\ gs[] \\ rveq \\ simp [GSYM PULL_EXISTS]
  \\ conj_tac
  >- (qexists_tac ‘c’ \\ gs[get_file_content_def,fastForwardFD_def]
      \\ rename [‘ALOOKUP fs.infds fd = SOME zz’]
      \\ PairCases_on ‘zz’
      \\ qmatch_assum_rename_tac ‘ALOOKUP _ _ = SOME (ino,mode,off')’
      \\ gs[] \\ simp[miscTheory.the_def,AFUPDKEY_ALOOKUP,MAX_DEF])
  \\ conj_tac
  >- (gs[get_mode_def,fastForwardFD_def,get_file_content_def]
      \\ rename [‘ALOOKUP fs.infds fd = SOME zz’]
      \\ PairCases_on ‘zz’
      \\ qmatch_assum_rename_tac ‘ALOOKUP _ _ = SOME (ino,mode,off')’
      \\ gs[] \\ simp[miscTheory.the_def,AFUPDKEY_ALOOKUP])
  \\ xsimpl \\ simp[fastForwardFD_eq_forwardFD] \\ xsimpl
QED

Theorem INSTREAM_LINES_fastForwardFD:
  STDIO (forwardFD fs fd x) * INSTREAM_LINES c0 fd is [] (forwardFD fs fd x) ==>>
  STDIO (fastForwardFD fs fd) * INSTREAM_LINES c0 fd is [] (fastForwardFD fs fd) * GC
Proof
  simp [INSTREAM_LINES_def]
  \\ xsimpl \\ rpt strip_tac
  \\ first_assum $ irule_at (Pos hd)
  \\ fs [implode_def]
  \\ simp [INSTREAM_STR_fastForwardFD]
QED

Definition find_surplus_fun_def:
  find_surplus_fun c (wl:word8 list) (i:num) (j:num) =
    if i = j ∨ LENGTH wl < i ∨ LENGTH wl < j then NONE else
    if ORD c = w2n (EL i wl) then SOME i else
      find_surplus_fun c wl (i+1) j
Termination
  WF_REL_TAC ‘measure (λ(c,wl,i,j). LENGTH wl + 1 - i)’
  \\ rw [] \\ gvs [NOT_LESS]
End

Theorem find_surplus:
  CHAR c cv ∧ NUM i iv ∧ NUM j jv ∧ i ≤ j ∧ j ≤ LENGTH wl ∧ av = Loc T a
  ⇒
  app (p:'ffi ffi_proj) TextIO_find_surplus_v [cv; av; iv; jv]
    (a ~~>> W8array wl)
    (POSTv retv.
        a ~~>> W8array wl *
        & (OPTION_TYPE NUM (find_surplus_fun c wl i j) retv))
Proof
  qid_spec_tac ‘iv’
  \\ qid_spec_tac ‘i’
  \\ completeInduct_on ‘LENGTH wl - i’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ xcf_with_def TextIO_find_surplus_v_def
  \\ xlet_auto >- xsimpl
  \\ simp [Once find_surplus_fun_def]
  \\ IF_CASES_TAC \\ gvs []
  \\ xif
  \\ first_x_assum $ irule_at $ Pos hd \\ simp []
  >- (xcon \\ gvs [std_preludeTheory.OPTION_TYPE_def] \\ xsimpl)
  \\ ‘i < LENGTH wl’ by gvs []
  \\ xlet ‘POSTv retv. a ~~>> W8array wl * cond (WORD (EL i wl) retv)’
  >- (xapp \\ simp [W8ARRAY_def] \\ xsimpl \\ metis_tac [])
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ ‘word8_to_char (EL i wl) = c ⇔ ORD c = w2n (EL i wl)’ by
   (gvs [(*CharProgTheory.fromByte_def*)]
    \\ Cases_on ‘EL i wl’ \\ gvs []
    \\ Cases_on ‘c’ \\ gvs [])
  \\ gvs []
  \\ IF_CASES_TAC \\ gvs []
  \\ xif
  \\ first_x_assum $ irule_at $ Pos hd \\ simp []
  >- (xcon \\ gvs [std_preludeTheory.OPTION_TYPE_def] \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ ‘LENGTH wl < (i+1) + LENGTH wl - i’ by gvs[]
  \\ last_x_assum drule
  \\ disch_then drule
  \\ impl_tac >- gvs []
  \\ strip_tac
  \\ xapp
QED

Theorem to_W8ARRAY[local]:
  loc ~~>> W8array bcontent = W8ARRAY (Loc T loc) bcontent
Proof
  gvs [W8ARRAY_def,cond_STAR,FUN_EQ_THM,SEP_EXISTS_THM]
QED

Theorem ind_surplus_fun_eq_NONE[local]:
  ∀c bcontent r w.
    w ≤ LENGTH bcontent ∧ r ≤ w ∧
    (∀i. r ≤ i ∧ i < w ⇒ w2n (EL i bcontent) ≠ ORD c) ⇒
    find_surplus_fun c bcontent r w = NONE
Proof
  ho_match_mp_tac find_surplus_fun_ind \\ rw []
  \\ simp [Once find_surplus_fun_def]
QED

Theorem ind_surplus_fun_eq_SOME[local]:
  ∀c bcontent r w.
    w ≤ LENGTH bcontent ∧ r ≤ j ∧ j < LENGTH bcontent ∧
    w2n (EL j bcontent) = ORD c ∧ r < w ∧ j < w ∧
    (∀i. r ≤ i ∧ i < j ⇒ w2n (EL i bcontent) ≠ ORD c) ⇒
    find_surplus_fun c bcontent r w = SOME j
Proof
  ho_match_mp_tac find_surplus_fun_ind \\ rw []
  \\ simp [Once find_surplus_fun_def]
  \\ Cases_on ‘r = j’ \\ gvs []
QED

Theorem inputUntil_1_not_found:
  CHAR c cv ∧ EVERY (λw. w2n w ≠ ORD c) bactive
  ⇒
  app (p:'ffi ffi_proj) TextIO_inputUntil_1_v [is; cv]
    (INSTREAM_BUFFERED_FD bactive fd is)
    (POSTv retv.
        INSTREAM_BUFFERED_FD [] fd is *
        & (SUM_TYPE STRING_TYPE STRING_TYPE
             (INL (implode (MAP (CHR o w2n) bactive))) retv))
Proof
  rw [] \\ gvs [PULL_FORALL]
  \\ xcf_with_def TextIO_inputUntil_1_v_def
  \\ simp[INSTREAM_BUFFERED_FD_def] \\ xpull \\ xmatch
  \\ simp [REF_NUM_def] \\ xpull
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ gvs [W8ARRAY_def] \\ xpull
  \\ xlet_auto \\ gvs []
  >- (xsimpl \\ gvs [instream_buffered_inv_def])
  \\ ‘find_surplus_fun c bcontent r w = NONE’ by
   (gvs [instream_buffered_inv_def]
    \\ irule ind_surplus_fun_eq_NONE
    \\ gvs [] \\ gvs [EVERY_EL,EL_TAKE,EL_DROP]
    \\ rw [] \\ qpat_x_assum ‘r ≤ i’ mp_tac
    \\ simp [LESS_EQ_EXISTS] \\ rw [] \\ gvs [])
  \\ gvs [std_preludeTheory.OPTION_TYPE_def]
  \\ xmatch
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ gvs [GSYM W8ARRAY_def]
  \\ gvs [to_W8ARRAY]
  \\ xlet_auto
  >- (xsimpl \\ gvs [instream_buffered_inv_def])
  \\ xcon \\ xsimpl
  \\ rpt $ first_assum $ irule_at Any
  \\ gvs [std_preludeTheory.SUM_TYPE_def]
  \\ pop_assum mp_tac \\ gvs [implode_def]
  \\ gvs [instream_buffered_inv_def]
QED

Theorem TAKE_LENGTH_ADD1[local]:
  TAKE (LENGTH xs + 1) (xs ++ y::ys) = xs ++ [y]
Proof
  ‘xs ++ y::ys = (xs ++ [y]) ++ ys’ by rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ ‘LENGTH xs + 1 = LENGTH (xs ++ [y])’ by gvs []
  \\ asm_rewrite_tac [TAKE_LENGTH_APPEND]
QED

Theorem inputUntil_1_found:
  CHAR c cv ∧ EVERY (λw. w2n w ≠ ORD c) bs1
  ⇒
  app (p:'ffi ffi_proj) TextIO_inputUntil_1_v [is; cv]
    (INSTREAM_BUFFERED_FD (bs1 ++ (n2w (ORD c))::bs2) fd is)
    (POSTv retv.
        INSTREAM_BUFFERED_FD bs2 fd is *
        & (SUM_TYPE STRING_TYPE STRING_TYPE
             (INR (implode (MAP (CHR o w2n) bs1 ++ [c]))) retv))
Proof
  rw [] \\ gvs [PULL_FORALL]
  \\ xcf_with_def TextIO_inputUntil_1_v_def
  \\ simp[INSTREAM_BUFFERED_FD_def] \\ xpull \\ xmatch
  \\ simp [REF_NUM_def] \\ xpull
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ gvs [W8ARRAY_def] \\ xpull
  \\ xlet_auto \\ gvs []
  >- (xsimpl \\ gvs [instream_buffered_inv_def])
  \\ ‘find_surplus_fun c bcontent r w = SOME (r + LENGTH bs1)’ by
   (gvs [instream_buffered_inv_def]
    \\ irule ind_surplus_fun_eq_SOME \\ gvs []
    \\ ‘r ≤ LENGTH bcontent’ by gvs []
    \\ drule LESS_EQ_LENGTH \\ strip_tac \\ gvs []
    \\ gvs [rich_listTheory.DROP_LENGTH_APPEND,EL_APPEND2]
    \\ simp [LESS_EQ_EXISTS,PULL_EXISTS]
    \\ gvs [LIST_EQ_REWRITE,ADD1,EL_TAKE,EVERY_EL]
    \\ rpt strip_tac
    >-
     (first_x_assum $ qspec_then ‘p’ mp_tac
      \\ gvs [EL_APPEND1] \\ metis_tac [])
    \\ first_x_assum $ qspec_then ‘LENGTH bs1’ mp_tac
    \\ rewrite_tac [APPEND,GSYM APPEND_ASSOC]
    \\ fs [EL_APPEND2] \\ disch_then $ assume_tac o SYM
    \\ gvs [ORD_BOUND])
  \\ gvs [std_preludeTheory.OPTION_TYPE_def]
  \\ xmatch
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ gvs [GSYM W8ARRAY_def]
  \\ gvs [to_W8ARRAY]
  \\ xlet_auto
  >- (xsimpl \\ gvs [instream_buffered_inv_def])
  \\ xcon \\ xsimpl
  \\ rpt $ first_assum $ irule_at Any
  \\ gvs [std_preludeTheory.SUM_TYPE_def]
  \\ pop_assum mp_tac \\ gvs [implode_def]
  \\ gvs [instream_buffered_inv_alt]
  \\ rewrite_tac [APPEND,GSYM APPEND_ASSOC,DROP_LENGTH_APPEND,TAKE_LENGTH_ADD1]
  \\ simp [implode_def] \\ strip_tac
  \\ qexists_tac ‘old ++ bs1 ++ [n2w (ORD c)]’ \\ gvs []
QED

Theorem not_EVERY_imp[local]:
  ∀xs. ¬EVERY p xs ⇒ ∃ys z zs. xs = ys ++ z::zs ∧ EVERY p ys ∧ ~ p z
Proof
  Induct \\ gvs [] \\ strip_tac \\ Cases_on ‘p h’ \\ gvs [] \\ rw [] \\ gvs []
  >- (qexists_tac ‘h::ys’ \\ gvs [])
  \\ qexists_tac ‘[]’ \\ gvs []
QED

Theorem inputUntil_1_spec:
  CHAR c cv
  ⇒
  app (p:'ffi ffi_proj) TextIO_inputUntil_1_v [is; cv]
    (INSTREAM_STR' fd is input fs non_empty is_empty)
    (POSTv retv.
        SEP_EXISTS bs1 bs2 is_empty1.
          INSTREAM_STR' fd is bs2 fs F is_empty1 *
          & (input = bs1 ++ bs2 ∧
             (non_empty ⇒ bs1 ≠ []) ∧
             (EVERY (λv. v ≠ c) bs1 ∧ is_empty1 ∧
              SUM_TYPE STRING_TYPE STRING_TYPE (INL (implode bs1)) retv
              ∨
              EVERY (λv. v ≠ c) (BUTLAST bs1) ∧ LAST bs1 = c ∧ bs1 ≠ [] ∧
              SUM_TYPE STRING_TYPE STRING_TYPE (INR (implode bs1)) retv)))
Proof
  gvs [INSTREAM_STR'_def] \\ rw [] \\ xpull \\ gvs []
  \\ Cases_on ‘EVERY (λv. v ≠ c) active’
  >-
   (xapp_spec inputUntil_1_not_found
    \\ gvs [PULL_EXISTS] \\ first_assum $ irule_at (Pos hd)
    \\ qexists_tac ‘fd’ \\ gvs []
    \\ qexists_tac ‘(MAP (n2w ∘ ORD) active)’ \\ gvs []
    \\ xsimpl \\ conj_tac
    >- gvs [EVERY_MEM,MEM_MAP,PULL_EXISTS,ORD_BOUND,ORD_11]
    \\ rw []
    \\ qexists_tac ‘active’ \\ gvs []
    \\ qexists_tac ‘T’ \\ gvs []
    \\ xsimpl \\ disj1_tac
    \\ gvs [MAP_MAP_o,o_DEF,ORD_BOUND])
  \\ drule not_EVERY_imp \\ strip_tac \\ gvs []
  \\ xapp_spec inputUntil_1_found
  \\ gvs [PULL_EXISTS] \\ first_assum $ irule_at (Pos hd)
  \\ qexists_tac ‘fd’ \\ gvs []
  \\ qexists_tac ‘(MAP (n2w ∘ ORD) zs)’ \\ gvs []
  \\ qexists_tac ‘(MAP (n2w ∘ ORD) ys)’ \\ gvs []
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ fs [EVERY_MAP,o_DEF,ORD_BOUND,ORD_11,MAP_MAP_o]
  \\ xsimpl \\ rw []
  \\ qexists_tac ‘STRCAT ys (STRING c "")’ \\ gvs []
  \\ qexists_tac ‘F’ \\ gvs []
  \\ qexists_tac ‘read' ++ ys ++ [c]’ \\ gvs []
  \\ qexists_tac ‘zs’ \\ gvs [] \\ xsimpl
  \\ asm_rewrite_tac [GSYM SNOC_APPEND,FRONT_SNOC]
QED

Theorem refillBuffer_with_read_spec_STR:
  app (p:'ffi ffi_proj) TextIO_refillBuffer_with_read_v [is]
    (STDIO fs * INSTREAM_STR' fd is input fs F T)
    (POSTv retv.
       SEP_EXISTS nr.
         STDIO (forwardFD fs fd nr) *
         INSTREAM_STR' fd is input (forwardFD fs fd nr) (~(NULL input)) (NULL input))
Proof
  simp [Once STDIO_def]
  \\ gvs [INSTREAM_STR'_def] \\ rw [] \\ xpull \\ gvs []
  \\ gvs [INSTREAM_BUFFERED_FD_def] \\ rw [] \\ xpull \\ gvs []
  \\ xapp_spec refillBuffer_with_read_spec \\ gvs []
  \\ ‘get_mode (fs with numchars := ll) fd = SOME ReadMode ∧
      get_file_content (fs with numchars := ll) fd = SOME (STRCAT read' input,STRLEN read')’
     by gvs [get_mode_def,get_file_content_def]
  \\ rpt $ first_assum $ irule_at $ Pos hd
  \\ gvs [INSTREAM_BUFFERED_BL_FD_def]
  \\ xsimpl \\ gvs [PULL_EXISTS]
  \\ rpt $ first_assum $ irule_at $ Pos hd
  \\ qexists_tac ‘emp’ \\ gvs [SEP_CLAUSES]
  \\ gvs [REF_NUM_def] \\ xsimpl \\ rw []
  \\ Cases_on ‘x = 0’ \\ gvs [NULL_EQ]
  >- (first_x_assum $ irule_at $ Pos hd \\ rw []
      \\ gvs [bumpFD_0,STDIO_def] \\ xsimpl
      \\ qexists_tac ‘THE (LTL ll)’ \\ gvs [] \\ xsimpl)
  \\ drule LESS_EQ_LENGTH \\ strip_tac \\ gvs []
  \\ irule_at Any EQ_REFL
  \\ qsuff_tac ‘explode_fromI (STRLEN ys1) (STRCAT (STRCAT read' ys1) ys2)
             (STRLEN read') = MAP (n2w ∘ ORD) ys1’
  >- (rw [] \\ gvs [] \\ first_x_assum $ irule_at $ Pos hd \\ rw []
      \\ gvs [bumpFD_forwardFD,fsFFIPropsTheory.forwardFD_numchars,STDIO_def]
      \\ xsimpl \\ qexists_tac ‘THE (LTL ll)’ \\ xsimpl
      \\ DEP_REWRITE_TAC [STD_streams_forwardFD] \\ gvs []
      \\ gvs [get_file_content_def] \\ PairCases_on ‘x’
      \\ gvs [get_mode_def]
      \\ gvs [STD_streams_def]
      \\ CCONTR_TAC \\ gvs []
      \\ first_x_assum $ qspecl_then [‘2’,‘WriteMode’,‘STRLEN err’] mp_tac
      \\ first_x_assum $ qspecl_then [‘1’,‘WriteMode’,‘STRLEN out’] mp_tac
      \\ gvs [])
  \\ gvs [explode_fromI_def,take_fromI_def]
  \\ ‘STRLEN read' = LENGTH ((MAP (n2w ∘ ORD) read'):word8 list)’ by gvs []
  \\ asm_rewrite_tac [DROP_LENGTH_APPEND,listTheory.TAKE_LENGTH_ID_rwt2,GSYM APPEND_ASSOC]
  \\ ‘STRLEN ys1 = LENGTH ((MAP (n2w ∘ ORD) ys1):word8 list)’ by simp []
  \\ asm_rewrite_tac [TAKE_LENGTH_APPEND,GSYM APPEND_ASSOC]
QED

Theorem refillBuffer_with_read_guard_spec_STR:
  app (p:'ffi ffi_proj) TextIO_refillBuffer_with_read_guard_v [is]
    (STDIO fs * INSTREAM_STR' fd is input fs F T)
    (POSTv retv.
       SEP_EXISTS nr.
         STDIO (forwardFD fs fd nr) *
         INSTREAM_STR' fd is input (forwardFD fs fd nr) (~(NULL input)) (NULL input) *
         & BOOL (NULL input) retv)
Proof
  rw [] \\ gvs [PULL_FORALL]
  \\ xcf_with_def TextIO_refillBuffer_with_read_guard_v_def
  \\ xlet_auto_spec (SOME refillBuffer_with_read_spec_STR)
  >-
   (qexists_tac ‘emp’ \\ qexists_tac ‘input’
    \\ qexists_tac ‘fs’ \\ qexists_tac ‘fd’ \\ xsimpl
    \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl)
  \\ gvs [INSTREAM_STR'_def,INSTREAM_BUFFERED_FD_def,REF_NUM_def] \\ xpull
  \\ xmatch
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xapp_spec (DISCH_ALL eq_v_thm |> GEN_ALL |> ISPEC “NUM”)
  \\ gvs [EqualityType_NUM_BOOL]
  \\ rpt $ first_assum $ irule_at Any
  \\ xsimpl \\ rw []
  \\ rpt $ first_assum $ irule_at Any
  \\ xsimpl
  \\ gvs [NULL_EQ]
  \\ gvs [instream_buffered_inv_alt]
  \\ Cases_on `active = ""` \\ gvs[]
QED

Theorem takeUnitlIncl_append:
  ∀bs1 bs2 p.
    EVERY (λx. ~p x) bs1 ⇒
    takeUntilIncl p (STRCAT bs1 bs2) =
    STRCAT bs1 (takeUntilIncl p bs2)
Proof
  Induct \\ gvs [takeUntilIncl_def]
QED

Theorem gen_inputLine_lem1:
  ∀bs1 bs2.
    EVERY (λv. v ≠ c) bs1 ⇒
    gen_inputLine c (STRCAT bs1 bs2) = implode bs1 ^ gen_inputLine c bs2 ∧
    dropUntilIncl ($= c) (STRCAT bs1 bs2) = dropUntilIncl ($= c) bs2
Proof
  Induct \\ gvs [dropUntilIncl_def,gen_inputLine_def]
  \\ rpt strip_tac \\ gvs [takeUntilIncl_def,implode_def,strcat_def,concat_def]
  >-
   (‘~EXISTS ($= c) bs1’ by (gvs [o_DEF] \\ gvs [EVERY_MEM])
    \\ asm_rewrite_tac [] \\ rw [] \\ irule takeUnitlIncl_append
    \\ gvs [EVERY_MEM])
  \\ gvs [mllistTheory.dropUntil_def]
QED

Theorem gen_inputLine_lem2:
  EVERY (λv. v ≠ LAST bs1) (FRONT bs1) ∧ bs1 ≠ "" ⇒
  gen_inputLine (LAST bs1) (STRCAT bs1 bs2) = implode bs1 ∧
  dropUntilIncl ($= (LAST bs1)) (STRCAT bs1 bs2) = bs2
Proof
  Cases_on ‘bs1’ using SNOC_CASES \\ gvs []
  \\ rewrite_tac [LAST_SNOC,FRONT_SNOC]
  \\ gvs [SNOC_APPEND]
  \\ rewrite_tac [GSYM APPEND_ASSOC]
  \\ simp_tac std_ss [gen_inputLine_lem1]
  \\ gvs [strcat_def,concat_def,implode_def]
  \\ gvs [gen_inputLine_def,takeUntilIncl_def,implode_def]
  \\ gvs [dropUntilIncl_def,mllistTheory.dropUntil_def]
QED

Theorem inputUntil_2_spec_STR_lemma[local]:
  ∀input acc accv fs.
    CHAR c cv ∧ LIST_TYPE STRING_TYPE acc accv ∧ acc ≠ []
    ⇒
    app (p:'ffi ffi_proj) TextIO_inputUntil_2_v [is; cv; accv]
      (STDIO fs * INSTREAM_STR' fd is input fs T F)
      (POSTv retv.
         SEP_EXISTS nr.
           STDIO (forwardFD fs fd nr) *
           INSTREAM_STR fd is (dropUntilIncl ($= c) input) (forwardFD fs fd nr) *
           & OPTION_TYPE STRING_TYPE
               (SOME $ concat (REVERSE acc) ^ gen_inputLine c input) retv)
Proof
  gen_tac \\ completeInduct_on ‘LENGTH input’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ xcf_with_def TextIO_inputUntil_2_v_def
  \\ xlet_auto_spec (SOME (inputUntil_1_spec |> Q.INST [‘non_empty’|->‘T’,‘is_empty’|->‘F’]))
  >- (rw [] \\ xsimpl \\ rw [] \\ qexists_tac ‘STDIO fs’ \\ xsimpl
      \\ qexists_tac ‘fs’ \\ xsimpl \\ rw []
      \\ irule_at (Pos hd) EQ_REFL \\ gvs []
      >- (qexists_tac ‘T’ \\ gvs [] \\ xsimpl)
      \\ qexists_tac ‘x''’ \\ gvs [] \\ xsimpl)
  \\ gvs []
  >~ [‘INL’] >-
   (gvs [std_preludeTheory.SUM_TYPE_def]
    \\ xmatch
    \\ xlet_auto_spec (SOME (refillBuffer_with_read_guard_spec_STR
                               |> Q.INST [‘non_empty’|->‘T’,‘is_empty’|->‘F’,‘input’|->‘bs2’]
                               |> ONCE_REWRITE_RULE [STAR_COMM]))
    >- (qexists_tac ‘emp’ \\ qexists_tac ‘fs’ \\ gvs []
        \\ xsimpl \\ gvs [] \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl \\ gvs [])
    \\ gvs []
    \\ reverse $ Cases_on ‘bs2 = []’ \\ gvs [BOOL_def]
    \\ xif
    >-
     (qexists_tac ‘F’ \\ gvs [BOOL_def,semanticPrimitivesTheory.Boolv_def]
      \\ conj_tac >- EVAL_TAC
      \\ xlet_auto >- (xcon \\ xsimpl)
      \\ last_x_assum $ qspecl_then [‘bs2’,‘implode bs1 :: acc’,‘v’,‘forwardFD fs fd nr’] mp_tac
      \\ impl_tac >- (Cases_on ‘bs1’ \\ gvs[])
      \\ impl_tac
      >- (gvs [] \\ EVAL_TAC \\ gvs [STRING_TYPE_def,implode_def])
      \\ strip_tac
      \\ xapp \\ qexists_tac ‘emp’ \\ xsimpl
      \\ gvs [concat_append,gen_inputLine_lem1,concat_sing,implode_def] \\ rw []
      \\ gvs [fsFFIPropsTheory.forwardFD_o]
      \\ qexists_tac ‘nr + x’ \\ gvs [] \\ xsimpl)
    \\ qexists_tac ‘T’ \\ gvs [BOOL_def,semanticPrimitivesTheory.Boolv_def]
    \\ conj_tac >- EVAL_TAC
    \\ xlet_auto >- (xcon \\ xsimpl)
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- (xcon \\ xsimpl)
    \\ ‘LIST_TYPE STRING_TYPE (str c :: implode bs1 :: acc) v'’ by gvs [LIST_TYPE_def]
    \\ xlet ‘POSTv retv. INSTREAM_STR' fd is "" (forwardFD fs fd nr) F T *
           STDIO (forwardFD fs fd nr) *
           & LIST_TYPE STRING_TYPE (REVERSE (str c::implode bs1::acc)) retv’
    >-
     (xapp_spec (ListProgTheory.reverse_v_thm |> GEN_ALL |> ISPEC “STRING_TYPE”)
      \\ gvs [] \\ pop_assum $ irule_at $ Pos hd \\ xsimpl)
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ gvs [concat_append,concat_sing]
    \\ ‘STRLEN bs1 + (strlen (concat (REVERSE acc)) + 1) = 1 ⇔ F’
          by (Cases_on ‘bs1’ \\ gvs []) \\ gvs []
    \\ xif \\ first_x_assum $ irule_at $ Pos hd \\ gvs []
    \\ xcon \\ xsimpl \\ gvs [std_preludeTheory.OPTION_TYPE_def]
    \\ qexists_tac ‘nr’
    \\ drule gen_inputLine_lem1
    \\ disch_then $ qspec_then ‘[]’ mp_tac \\ gvs []
    \\ gvs [dropUntilIncl_def,mllistTheory.dropUntil_def,gen_inputLine_def]
    \\ gvs [str_def,implode_def] \\ strip_tac
    \\ gvs [INSTREAM_STR_def,INSTREAM_STR'_def]
    \\ xsimpl \\ rpt gen_tac \\ strip_tac
    \\ gvs [] \\ xsimpl)
  \\ gvs [std_preludeTheory.SUM_TYPE_def]
  \\ xmatch
  \\ xlet ‘POSTv retv. INSTREAM_STR' fd is bs2 fs F is_empty1 * STDIO fs *
           & STRING_TYPE (concat (REVERSE (implode bs1::acc))) retv’
  >-
   (Cases_on ‘acc’ \\ gvs [LIST_TYPE_def]
    \\ xmatch \\ xlet_auto >- (xcon \\ xsimpl)
    \\ ‘LIST_TYPE STRING_TYPE (implode bs1 :: h :: t) v’ by gvs [LIST_TYPE_def]
    \\ xlet ‘POSTv retv. INSTREAM_STR' fd is bs2 fs F is_empty1 * STDIO fs *
             & LIST_TYPE STRING_TYPE (REVERSE (implode bs1::h::t)) retv’
    >-
     (xapp_spec (ListProgTheory.reverse_v_thm |> GEN_ALL |> ISPEC “STRING_TYPE”)
      \\ gvs [] \\ pop_assum $ irule_at $ Pos hd \\ xsimpl)
    \\ xapp \\ pop_assum $ irule_at Any \\ xsimpl)
  \\ xcon \\ xsimpl \\ gvs [std_preludeTheory.OPTION_TYPE_def]
  \\ qexists_tac ‘0’
  \\ gvs [forwardFD_0,gen_inputLine_lem2,concat_append,concat_sing]
  \\ gvs [INSTREAM_STR_def,INSTREAM_STR'_def]
  \\ xsimpl \\ rpt gen_tac \\ strip_tac
  \\ rename [‘STRCAT y1 y2 = STRCAT _ _’]
  \\ qexists_tac ‘y1’
  \\ qexists_tac ‘y2’
  \\ gvs [] \\ xsimpl
QED

Theorem inputUntil_2_spec_STR:
  CHAR c cv ∧ LIST_TYPE STRING_TYPE [] accv
  ⇒
  app (p:'ffi ffi_proj) TextIO_inputUntil_2_v [is; cv; accv]
    (STDIO fs * INSTREAM_STR fd is input fs)
    (POSTv retv.
       SEP_EXISTS nr.
         STDIO (forwardFD fs fd nr) *
         INSTREAM_STR fd is (dropUntilIncl ($= c) input) (forwardFD fs fd nr) *
         & OPTION_TYPE STRING_TYPE
             (if input = "" then NONE else SOME $ gen_inputLine c input) retv)
Proof
  strip_tac \\ gvs [PULL_FORALL]
  \\ xcf_with_def TextIO_inputUntil_2_v_def
  \\ xlet_auto_spec (SOME (inputUntil_1_spec
                             |> Q.INST [‘non_empty’|->‘F’,‘is_empty’|->‘F’]
                             |> REWRITE_RULE [INSTREAM_STR'_F_F]))
  >- (rw [] \\ xsimpl \\ rw [] \\ qexists_tac ‘STDIO fs’ \\ xsimpl
      \\ qexists_tac ‘input’ \\ qexists_tac ‘fs’ \\ qexists_tac ‘fd’ \\ xsimpl
      \\ rw []
      \\ qexists_tac ‘x’ \\ qexists_tac ‘x'’ \\ gvs []
      >- (qexists_tac ‘T’ \\ gvs [] \\ xsimpl)
      \\ qexists_tac ‘x''’ \\ gvs [] \\ xsimpl)
  \\ gvs []
  >~ [‘INL’] >-
   (gvs [std_preludeTheory.SUM_TYPE_def]
    \\ xmatch
    \\ xlet_auto_spec (SOME (refillBuffer_with_read_guard_spec_STR
                               |> Q.INST [‘non_empty’|->‘T’,‘is_empty’|->‘F’,‘input’|->‘bs2’]
                               |> ONCE_REWRITE_RULE [STAR_COMM]))
    >- (qexists_tac ‘emp’ \\ qexists_tac ‘fs’
        \\ qexists_tac ‘fd’ \\ qexists_tac ‘bs2’ \\ gvs []
        \\ xsimpl \\ gvs [] \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl \\ gvs [])
    \\ gvs []
    \\ reverse xif
    >-
     (xlet_auto >- (xcon \\ xsimpl)
      \\ ‘LIST_TYPE STRING_TYPE [implode bs1] v’ by gvs [LIST_TYPE_def]
      \\ mp_tac inputUntil_2_spec_STR_lemma
      \\ disch_then (drule_then drule) \\ gvs []
      \\ disch_then $ qspecl_then [‘bs2’,‘forwardFD fs fd nr’] assume_tac
      \\ xapp \\ qexists_tac ‘emp’ \\ xsimpl
      \\ gvs [concat_append,gen_inputLine_lem1,concat_sing,implode_def] \\ rw []
      \\ gvs [fsFFIPropsTheory.forwardFD_o]
      \\ qexists_tac ‘nr + x’ \\ gvs [] \\ xsimpl)
    \\ xlet_auto >- (xcon \\ xsimpl)
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- (xcon \\ xsimpl)
    \\ ‘LIST_TYPE STRING_TYPE (str c :: implode bs1 :: []) v'’ by gvs [LIST_TYPE_def]
    \\ xlet ‘POSTv retv. INSTREAM_STR' fd is "" (forwardFD fs fd nr) F T *
           STDIO (forwardFD fs fd nr) *
           & LIST_TYPE STRING_TYPE (REVERSE (str c::implode bs1::[])) retv’
    >-
     (xapp_spec (ListProgTheory.reverse_v_thm |> GEN_ALL |> ISPEC “STRING_TYPE”)
      \\ gvs [] \\ pop_assum $ irule_at $ Pos hd \\ xsimpl)
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ gvs [concat_append,concat_sing]
    \\ xif
    >-
     (xcon \\ xsimpl \\ gvs [concat_def,implode_def,str_def]
      \\ gvs [std_preludeTheory.OPTION_TYPE_def]
      \\ gvs [dropUntilIncl_def,mllistTheory.dropUntil_def,gen_inputLine_def]
      \\ gvs [INSTREAM_STR_def,INSTREAM_STR'_def]
      \\ xsimpl \\ qexists_tac ‘nr’
      \\ rpt gen_tac \\ strip_tac
      \\ gvs [] \\ xsimpl)
    \\ xcon \\ xsimpl
    \\ ‘bs1 ≠ []’ by (Cases_on ‘bs1’ \\ gvs [concat_def,str_def,implode_def])
    \\ gvs [std_preludeTheory.OPTION_TYPE_def]
    \\ qexists_tac ‘nr’
    \\ drule gen_inputLine_lem1
    \\ disch_then $ qspec_then ‘[]’ mp_tac \\ gvs []
    \\ strip_tac \\ gvs []
    \\ gvs [dropUntilIncl_def,mllistTheory.dropUntil_def,gen_inputLine_def]
    \\ gvs [str_def,implode_def,concat_def,strcat_def]
    \\ gvs [INSTREAM_STR_def,INSTREAM_STR'_def]
    \\ xsimpl \\ rpt gen_tac \\ strip_tac
    \\ gvs [] \\ xsimpl)
  \\ gvs [std_preludeTheory.SUM_TYPE_def]
  \\ xmatch
  \\ xlet ‘POSTv retv. INSTREAM_STR' fd is bs2 fs F is_empty1 * STDIO fs *
                       & STRING_TYPE (implode bs1) retv’
  >- (gvs [LIST_TYPE_def] \\ xmatch \\ xvar \\ xsimpl)
  \\ xcon \\ xsimpl \\ gvs [std_preludeTheory.OPTION_TYPE_def]
  \\ qexists_tac ‘0’
  \\ gvs [forwardFD_0,gen_inputLine_lem2,concat_append,concat_sing]
  \\ gvs [INSTREAM_STR_def,INSTREAM_STR'_def]
  \\ xsimpl \\ rpt gen_tac \\ strip_tac
  \\ rename [‘STRCAT y1 y2 = STRCAT _ _’]
  \\ qexists_tac ‘y1’
  \\ qexists_tac ‘y2’
  \\ gvs [] \\ xsimpl
QED

Theorem dropUntilIncl_empty:
  EVERY (λc. c ≠ c0) ls ⇒
  dropUntilIncl ($= c0) ls = ""
Proof
  Cases_on`ls` >-
    EVAL_TAC>>
  rw[]>>
  DEP_REWRITE_TAC[NOT_EXISTS_FRONT_dropUntilIncl_eq_nil]>>
  fs[o_DEF,EVERY_MEM,MEM_FRONT]>>
  metis_tac[MEM_FRONT,MEM]
QED

Theorem dropUntilIncl_cons:
  dropUntilIncl P (x::xs) =
  if P x then xs
  else dropUntilIncl P xs
Proof
  EVAL_TAC>>rw[]>>
  EVAL_TAC
QED

Theorem takeUntilIncl_cons2:
  takeUntilIncl P (x::xs) =
  if P x then [x]
  else x::takeUntilIncl P xs
Proof
  EVAL_TAC>>rw[]
QED

Theorem implode_cons_str:
  str c ^ implode cs =
  implode (c::cs)
Proof
  rw[implode_def,strcat_def,concat_def,str_def]>>
  TOP_CASE_TAC>>rw[]
QED

Theorem gen_inputLine_cons:
  gen_inputLine c (x::xs) =
  if x = c then str c else str x ^ gen_inputLine c xs
Proof
  rw[gen_inputLine_def]>>
  gvs[takeUntilIncl_cons2,str_def,implode_cons_str]>>
  gvs[EVERY_MEM,EXISTS_MEM]
QED

Theorem inputLine_spec_STR[local]:
  CHAR c0 c0v /\
  EVERY (\c. c <> c0) to_read /\
  (text <> "" ==> HD text = c0) ==>
  app (p:'ffi ffi_proj) TextIO_inputLine_v [c0v; is]
    (STDIO fs * INSTREAM_STR fd is (to_read ++ text) fs)
    (POSTv v. SEP_EXISTS k.
                cond (OPTION_TYPE STRING_TYPE
                        (case to_read of
                         | [] => (if text = "" then NONE else SOME (str c0))
                         | _ => SOME (implode (to_read ++ [c0]))) v) *
                STDIO (forwardFD fs fd k) *
                INSTREAM_STR fd is (TL text) (forwardFD fs fd k))
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_inputLine_v_def
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ xapp_spec inputUntil_2_spec_STR
  \\ simp[LIST_TYPE_def]
  \\ goal_assum drule
  \\ qexists_tac`emp`
  \\ qexists_tac`STRCAT to_read text`
  \\ qexists_tac`fs`
  \\ qexists_tac`fd`
  \\ xsimpl
  \\ rw[]
  >- (
    simp[dropUntilIncl_empty]>>
    qexists_tac`x`>>xsimpl)
  >- (
    simp[dropUntilIncl_empty]>>
    qexists_tac`x`>>xsimpl>>
    every_case_tac>>gvs[gen_inputLine_def]>>
    `~EXISTS ($= c0) t` by
      gvs[o_DEF,EVERY_MEM]>>
    gvs[])>>
  qexists_tac`x`>>xsimpl>>
  every_case_tac>>gvs[]
  >- (
    Cases_on`text`>>gvs[gen_inputLine_def]>>
    fs[takeUntilIncl_def,dropUntilIncl_def,mllistTheory.dropUntil_def,str_def]>>
    xsimpl)>>
  gvs[gen_inputLine_cons,dropUntilIncl_cons]>>
  drule gen_inputLine_lem1>>
  disch_then(qspec_then`text` assume_tac)>>gvs[]>>
  Cases_on`text`>>gvs[gen_inputLine_def]>>
  fs[takeUntilIncl_def,dropUntilIncl_def,mllistTheory.dropUntil_def,str_def]>>
  xsimpl>>
  simp[GSYM implode_cons_str]>>
  simp[str_def]>>
  fs[implode_STRCAT,implode_def]
QED

Theorem inputLineTokens_spec_STR[local]:
  CHAR c0 c0v ∧
  (CHAR --> BOOL) f fv ∧
  (STRING_TYPE --> (a:'a->v->bool)) g gv ∧
  EVERY (\c. c <> c0) to_read /\
  (text <> "" ==> HD text = c0) ∧
  f c0 ==>
  app (p:'ffi ffi_proj) TextIO_inputLineTokens_v [c0v; is; fv; gv]
    (STDIO fs * INSTREAM_STR fd is (to_read ++ text) fs)
    (POSTv v. SEP_EXISTS k.
                cond (OPTION_TYPE (LIST_TYPE a)
                        (OPTION_MAP (MAP g o tokens f)
                          (if NULL text ∧ NULL to_read then NONE
                           else SOME (implode to_read))) v) *
                STDIO (forwardFD fs fd k) *
                INSTREAM_STR fd is (TL text) (forwardFD fs fd k))
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_inputLineTokens_v_def
  \\ xlet_auto_spec (SOME inputLine_spec_STR)
  >- (
    qexists_tac`emp`>>
    qexists_tac`fs`>>
    qexists_tac`fd`>>
    xsimpl>>rw[]
    >-
      (qexists_tac`x`>>xsimpl)>>
    qexists_tac`x`>>xsimpl)>>
  pop_assum mp_tac>>reverse TOP_CASE_TAC
  >- (
    strip_tac>>
    gvs[std_preludeTheory.OPTION_TYPE_def]>>
    xmatch>>
    xlet_auto >- xsimpl>>
    xlet_auto >- xsimpl>>
    xcon>>xsimpl>>
    qexists_tac`k`>>xsimpl>>
    `TOKENS f (STRCAT (h::t) (STRING c0 "")) = TOKENS f (h :: t)` by
      (DEP_REWRITE_TAC[TOKENS_APPEND]>>gvs[]>>
      EVAL_TAC)>>
    gvs[TOKENS_eq_tokens_sym])>>
  IF_CASES_TAC>>
  gvs[NULL_EQ,std_preludeTheory.OPTION_TYPE_def]>>
  strip_tac>>xmatch
  >- (
    xcon>>xsimpl>>
    qexists_tac`k`>>xsimpl)>>
  xlet_auto >- xsimpl>>
  xlet_auto >- xsimpl>>
  xcon>>xsimpl>>
  qexists_tac`k`>>xsimpl>>
  pop_assum mp_tac>>
  simp[TOKENS_eq_tokens_sym]>>
  EVAL_TAC>>gvs[TOKENS_def,LIST_TYPE_def]
QED

Theorem inputLineTokens_spec_lines:
  CHAR c0 c0v ∧
  (CHAR --> BOOL) f fv ∧ (STRING_TYPE --> (a:'a->v->bool)) g gv ∧ f c0 ⇒
  app (p:'ffi ffi_proj) TextIO_inputLineTokens_v [c0v; is; fv; gv]
     (STDIO fs * INSTREAM_LINES c0 fd is lines fs)
     (POSTv v.
       SEP_EXISTS k.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES c0 fd is (TL lines) (forwardFD fs fd k) *
         & (OPTION_TYPE (LIST_TYPE a)
             (OPTION_MAP (MAP g o tokens f) (oHD lines)) v))
Proof
  rpt strip_tac
  \\ fs [INSTREAM_LINES_def] \\ xpull
  \\ xapp_spec inputLineTokens_spec_STR \\ rveq
  \\ strip_assume_tac (Q.SPEC ‘rest’ split_exists)
  \\ simp[PULL_EXISTS]
  \\ goal_assum drule \\ goal_assum drule
  \\ goal_assum drule \\ goal_assum drule
  \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac ‘g’
  \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac ‘fs’
  \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac ‘fd’
  \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac ‘a’
  \\ xsimpl \\ fs [] \\ rpt strip_tac
  \\ qexists_tac ‘x’ \\ qexists_tac ‘TL text’ \\ xsimpl
  \\ reverse (Cases_on ‘to_read = "" ==> text <> ""’) \\ fs []
  THEN1 (EVAL_TAC \\ fs [std_preludeTheory.OPTION_TYPE_def])
  \\ Cases_on ‘text = ""’ \\ fs []
  \\ fs [lines_of_gen_def]
  THEN1
   (‘~EXISTS ($= c0) to_read’ by fs [EXISTS_MEM,EVERY_MEM]
    \\ drule splitlines_at_not_exists2 \\ fs []
    \\ fs [strcat_def,concat_def,implode_def,str_def]
    \\ fs [TOKENS_eq_tokens_sym,o_DEF]
    \\ fs [stringTheory.TOKENS_APPEND,stringTheory.TOKENS_def]
    \\ Cases_on ‘to_read’ \\ fs [])
  \\ Cases_on ‘to_read = []’ \\ fs []
  THEN1
   (Cases_on ‘text’ \\ fs [] \\ fs [splitlines_at_hd_c0]
    \\ fs [strcat_def,concat_def,implode_def]
    \\ qpat_x_assum ‘OPTION_TYPE _ _ _’ mp_tac \\ EVAL_TAC
    \\ fs [] \\ EVAL_TAC)
  \\ ‘EXISTS ($= c0) rest’ by (fs [] \\ Cases_on ‘text’ \\ fs [])
  \\ drule splitlines_at_takeUntil_exists2 \\ fs []
  \\ ‘takeUntil ($= c0) (STRCAT to_read text) = to_read’ by
   (‘~EXISTS ($= c0) to_read’ by fs [EXISTS_MEM,EVERY_MEM]
    \\ drule takeUntil_append_not_exists_l \\ fs []
    \\ Cases_on ‘text’ \\ fs [] \\ EVAL_TAC)
  \\ ‘DROP (SUC (STRLEN to_read)) (STRCAT to_read text) = TL text’ by
   (Cases_on ‘text’ \\ fs []
    \\ qmatch_goalsub_abbrev_tac ‘DROP k (xs ++ ys)’
    \\ qsuff_tac ‘k = LENGTH xs’ \\ fs [DROP_LENGTH_APPEND]
    \\ unabbrev_all_tac \\ fs [])
  \\ rw []
  \\ qpat_x_assum ‘OPTION_TYPE _ _ _’ mp_tac
  \\ fs [TOKENS_eq_tokens_sym,o_DEF]
  \\ fs [stringTheory.TOKENS_APPEND,stringTheory.TOKENS_def]
  \\ fs [] \\ Cases_on ‘to_read’ \\ fs [strcat_def,concat_def,implode_def]
QED

Theorem inputAllTokens_aux_spec:
  ∀lines acc accv fs.
    CHAR c0 c0v ∧
    (CHAR --> BOOL) f fv ∧ (STRING_TYPE --> (a:'a->v->bool)) g gv ∧ f c0 ∧
    LIST_TYPE (LIST_TYPE a) acc accv ⇒
    app (p:'ffi ffi_proj) TextIO_inputAllTokens_aux_v
     [c0v; is; fv; gv; accv]
     (STDIO fs * INSTREAM_LINES c0 fd is lines fs)
       (POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES c0 fd is [] (forwardFD fs fd k) *
                & LIST_TYPE (LIST_TYPE a)
                    (REVERSE acc ++ MAP (MAP g o tokens f) lines) v)
Proof
  gen_tac \\ completeInduct_on `LENGTH lines`
  \\ rpt strip_tac
  \\ xcf_with_def TextIO_inputAllTokens_aux_v_def
  \\ rveq \\ fs [PULL_FORALL]
  \\ xlet `POSTv v.
       SEP_EXISTS k.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES c0 fd is (TL lines) (forwardFD fs fd k) *
         & (OPTION_TYPE (LIST_TYPE a)
             (OPTION_MAP (MAP g o tokens f) (oHD lines)) v)`
  THEN1 (xapp_spec inputLineTokens_spec_lines \\ fs [])
  \\ Cases_on `lines` \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq
  \\ xmatch \\ fs []
  THEN1
   (xapp_spec (ListProgTheory.reverse_v_thm |> GEN_ALL |> Q.ISPEC ‘LIST_TYPE (a:'a->v->bool)’)
    \\ asm_exists_tac \\ fs [] \\ xsimpl \\ rw []
    \\ qexists_tac ‘k’ \\ xsimpl)
  \\ xlet_auto THEN1 (xcon \\ xsimpl \\ fs [])
  \\ rveq \\ fs []
  \\ xapp
  \\ qexists_tac `emp` \\ xsimpl
  \\ qexists_tac `t` \\ qexists_tac `forwardFD fs fd k`
  \\ qexists_tac `MAP g (tokens f h)::acc`
  \\ fs [LIST_TYPE_def] \\ xsimpl \\ rw []
  \\ qexists_tac `x+k`
  \\ fs [forwardFD_o] \\ xsimpl
  \\ pop_assum mp_tac
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
QED

Theorem inputAllTokens_spec:
   CHAR c0 c0v ∧
   (CHAR --> BOOL) f fv ∧ (STRING_TYPE --> (a:'a->v->bool)) g gv ∧ f c0 ⇒
   app (p:'ffi ffi_proj) TextIO_inputAllTokens_v
     [c0v; is; fv; gv]
     (STDIO fs * INSTREAM_LINES c0 fd is lines fs)
       (POSTv v.
          STDIO (fastForwardFD fs fd) *
          INSTREAM_LINES c0 fd is [] (fastForwardFD fs fd) *
          & LIST_TYPE (LIST_TYPE a) (MAP (MAP g o tokens f) lines) v)
Proof
  rw []
  \\ xcf_with_def TextIO_inputAllTokens_v_def
  \\ xlet_auto
  THEN1 (xcon \\ xsimpl \\ fs [])
  \\ xapp_spec inputAllTokens_aux_spec
  \\ rpt (first_x_assum (irule_at Any))
  \\ qexists_tac `lines`
  \\ qexists_tac `fs`
  \\ qexists_tac `fd`
  \\ qexists_tac `[]`
  \\ qexists_tac `emp`
  \\ xsimpl
  \\ conj_tac >- fs [LIST_TYPE_def]
  \\ rw [INSTREAM_LINES_def]
  \\ xsimpl \\ rw[] \\ gs[lines_of_gen_def,implode_def] \\ rveq
  \\ fs [INSTREAM_STR_fastForwardFD]
QED

Theorem inputAllTokensFile_spec:
   CHAR c0 c0v ∧
   FILENAME fname fnamev ∧ hasFreeFD fs ∧
   (CHAR --> BOOL) f fv ∧ (STRING_TYPE --> (a:'a->v->bool)) g gv ∧ f c0
   ⇒
   app (p:'ffi ffi_proj) TextIO_inputAllTokensFile_v
     [c0v; fnamev; fv; gv]
     (STDIO fs)
     (POSTv sv. &OPTION_TYPE (LIST_TYPE (LIST_TYPE a))
            (if inFS_fname fs fname then
               SOME(MAP (MAP g o tokens f) (all_lines_file_gen c0 fs fname))
             else NONE) sv * STDIO fs)
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_inputAllTokensFile_v_def
  \\ reverse (Cases_on `STD_streams fs`)
  >- (fs [STDIO_def] \\ xpull)
  \\ reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def] \\ xpull \\ metis_tac[])
  \\ reverse IF_CASES_TAC
  >- (
    xhandle`POSTe ev. &BadFileName_exn ev * STDIO fs`
    >- (xlet_auto_spec (SOME openIn_STDIO_spec) \\ xsimpl)
    \\ fs[BadFileName_exn_def] \\ xcases \\ rw[]
    \\ xcon \\ xsimpl \\ fs [std_preludeTheory.OPTION_TYPE_def])
  \\ qmatch_goalsub_abbrev_tac`$POSTv Qval`
  \\ xhandle`$POSTv Qval` \\ xsimpl
  \\ xlet_auto_spec (SOME openIn_spec_lines) \\ xsimpl
  \\ unabbrev_all_tac
  \\ qabbrev_tac `fs1 = openFileFS fname fs ReadMode 0`
  \\ xlet `(POSTv v.
                STDIO (fastForwardFD fs1 (nextFD fs)) *
                INSTREAM_LINES c0 (nextFD fs) is [] (fastForwardFD fs1 (nextFD fs)) *
                & LIST_TYPE (LIST_TYPE a)
                    (MAP (MAP g o tokens f) (all_lines_file_gen c0 fs fname)) v)`
  THEN1
   (xapp_spec inputAllTokens_spec
    \\ rpt (first_x_assum (irule_at Any))
    \\ qexists_tac `all_lines_file_gen c0 fs fname`
    \\ qexists_tac `fs1`
    \\ qexists_tac `nextFD fs`
    \\ qexists_tac `emp`
    \\ xsimpl \\ rw [])
  \\ xlet `POSTv v. STDIO fs`
  THEN1
   (xapp_spec closeIn_spec_lines
    \\ qexists_tac `emp`
    \\ qexists_tac `[]`
    \\ qexists_tac `fastForwardFD fs1 (nextFD fs)`
    \\ qexists_tac `nextFD fs`
    \\ qexists_tac `c0`
    \\ xsimpl
    \\ conj_tac THEN1
     (fs [forwardFD_def,Abbr`fs1`]
      \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
      \\ imp_res_tac fsFFIPropsTheory.STD_streams_nextFD \\ fs [])
    \\ `validFileFD (nextFD fs) (fastForwardFD fs1 (nextFD fs)).infds` by
      (simp[validFileFD_fastForwardFD]>> simp[Abbr`fs1`]
       \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
       \\ match_mp_tac validFileFD_nextFD \\ fs [])
    \\ xsimpl \\ rw [Abbr`fs1`,fsFFIPropsTheory.forwardFD_ADELKEY_same]
    \\ imp_res_tac LESS_IMP_LESS_OR_EQ
    \\ imp_res_tac fsFFIPropsTheory.nextFD_leX \\ fs []
    \\ drule fsFFIPropsTheory.openFileFS_ADELKEY_nextFD
    \\ fs [] \\ xsimpl)
  \\ xcon \\ xsimpl
  \\ fs [std_preludeTheory.OPTION_TYPE_def]
QED

Theorem open_option_SOME_fail:
  OPTION_TYPE FILENAME (SOME s) fnv ∧ ~inFS_fname fs s ∧ hasFreeFD fs ⇒
  app (p:'ffi ffi_proj) TextIO_open_option_v [fnv]
    (STDIO fs)
    (POSTv retv. STDIO fs * & (OPTION_TYPE a NONE retv))
Proof
  rpt strip_tac \\ fs []
  \\ gvs [std_preludeTheory.OPTION_TYPE_def]
  \\ rename [‘FILENAME s sv’]
  \\ xcf_with_def TextIO_open_option_v_def
  \\ xmatch
  \\ reverse (xhandle ‘(POSTve
            (λis.
                 &(validFD (nextFD fs) (openFileFS s fs ReadMode 0) ∧
                  inFS_fname fs s) * INSTREAM_BUFFERED_FD [] (nextFD fs) is *
                 STDIO (openFileFS s fs ReadMode 0))
            (λe. &(BadFileName_exn e ∧ ¬inFS_fname fs s) * STDIO fs))’)
  THEN1 (gvs [BadFileName_exn_def] \\ xcases \\ xcon \\ xsimpl)
  THEN1 (xsimpl)
  \\ xlet ‘(POSTve
            (λis.
                 &(validFD (nextFD fs) (openFileFS s fs ReadMode 0) ∧
                  inFS_fname fs s) * INSTREAM_BUFFERED_FD [] (nextFD fs) is *
                 STDIO (openFileFS s fs ReadMode 0))
            (λe. &(BadFileName_exn e ∧ ¬inFS_fname fs s) * STDIO fs))’
  THEN1 (xapp_spec openIn_STDIO_spec \\ fs [])
  \\ xsimpl
QED

Definition sub_spec_def:
  sub_spec f p is fd =
          ∀fs text v.
            UNIT_TYPE () v ∧ fd ≥ 3 ∧ fd ≤ fs.maxFD ∧ validFileFD fd fs.infds ⇒
            app (p:'ffi ffi_proj) f [v] (STDIO fs * INSTREAM_STR fd is text fs)
              (POSTv u.
                 &(UNIT_TYPE () u ∧ validFileFD fd fs.infds) *
                 STDIO (fs with infds updated_by ADELKEY fd))
End

Theorem open_option_SOME:
  OPTION_TYPE FILENAME (SOME s) fnv ∧ inFS_fname fs s ∧ hasFreeFD fs ∧
  file_content fs s = SOME text ⇒
  app (p:'ffi ffi_proj) TextIO_open_option_v [fnv]
    (STDIO fs)
    (POSTv retv. SEP_EXISTS is f.
       STDIO (openFileFS s fs ReadMode 0) *
       INSTREAM_STR (nextFD fs) is text (openFileFS s fs ReadMode 0) *
       & (OPTION_TYPE (PAIR_TYPE (λx v. v = is) (λx v. v = f)) (SOME ((),())) retv ∧
          sub_spec f p is (nextFD fs)))
Proof
  rpt strip_tac \\ fs []
  \\ gvs [std_preludeTheory.OPTION_TYPE_def]
  \\ rename [‘FILENAME s sv’]
  \\ xcf_with_def TextIO_open_option_v_def
  \\ xmatch
  \\ reverse (xhandle ‘
    (POSTv retv. SEP_EXISTS is f.
       STDIO (openFileFS s fs ReadMode 0) *
       INSTREAM_STR (nextFD fs) is text (openFileFS s fs ReadMode 0) *
       & (OPTION_TYPE (PAIR_TYPE (λx v. v = is) (λx v. v = f)) (SOME ((),())) retv ∧
          sub_spec f p is (nextFD fs)))’)
  THEN1 (xsimpl \\ gvs [std_preludeTheory.OPTION_TYPE_def] \\ rw []
         \\ first_x_assum $ irule_at Any \\ fs [] \\ xsimpl)
  \\ drule (GEN_ALL openIn_spec_str)
  \\ disch_then (drule_at Any) \\ fs []
  \\ disch_then (assume_tac o SPEC_ALL)
  \\ xlet_auto THEN1 xsimpl
  \\ xfun_spec `f` ‘sub_spec f p is (nextFD fs)’
  THEN1
   (rw [sub_spec_def] \\ first_x_assum irule
    \\ gvs [UNIT_TYPE_def]
    \\ xmatch
    \\ xapp_spec closeIn_spec_str
    \\ qexists_tac `emp`
    \\ qexists_tac `text'`
    \\ qexists_tac `fs'`
    \\ qexists_tac `nextFD fs`
    \\ xsimpl \\ gvs [UNIT_TYPE_def])
  \\ xlet_auto
  THEN1 (xcon \\ xsimpl)
  \\ gvs []
  \\ xcon
  \\ xsimpl
  \\ gvs [std_preludeTheory.OPTION_TYPE_def,PAIR_TYPE_def]
  \\ xsimpl
QED

Definition sub_spec_none_def:
  sub_spec_none f p is =
          ∀fs text v k.
            UNIT_TYPE () v ⇒
            app (p:'ffi ffi_proj) f [v]
              (STDIO (forwardFD fs 0 k) *
               INSTREAM_STR 0 is text (forwardFD fs 0 k))
              (POSTv u. STDIO (fastForwardFD fs 0))
End

Theorem consume_rest_spec:
  ∀s fs fd k.
    app (p:'ffi ffi_proj) TextIO_consume_rest_v [is]
      (STDIO (forwardFD fs fd k) * INSTREAM_STR fd is s (forwardFD fs fd k))
      (POSTv retv. STDIO (fastForwardFD fs fd))
Proof
  Induct
  THEN1
   (rw[]
    \\ xcf_with_def TextIO_consume_rest_v_def
    \\ xlet ‘(POSTv chv.
          STDIO (fastForwardFD fs fd) *
          INSTREAM_STR fd is "" (fastForwardFD fs fd) *
          &OPTION_TYPE CHAR NONE chv)’
    THEN1
     (xapp_spec (input1_spec_str |> Q.INST [‘s’|->‘[]’] )
      \\ qexists_tac ‘emp’
      \\ qexists_tac ‘forwardFD fs fd k’
      \\ qexists_tac ‘fd’
      \\ xsimpl \\ rw [fsFFIPropsTheory.forwardFD_o]
      \\ irule SEP_IMP_TRANS
      \\ irule_at Any INSTREAM_STR_fastForwardFD
      \\ xsimpl)
    \\ gvs [std_preludeTheory.OPTION_TYPE_def]
    \\ xmatch \\ xvar \\ fs [INSTREAM_STR_fastForwardFD]
    \\ xsimpl)
  \\ rw[]
  \\ xcf_with_def TextIO_consume_rest_v_def
  \\ xlet ‘(POSTv chv. SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_STR fd is s (forwardFD fs fd k) *
            &OPTION_TYPE CHAR (SOME h) chv)’
  THEN1
   (xapp_spec (input1_spec_str |> Q.INST [‘s’|->‘STRING h s’] )
    \\ qexists_tac ‘emp’
    \\ qexists_tac ‘s’
    \\ qexists_tac ‘h’
    \\ qexists_tac ‘(forwardFD fs fd k)’
    \\ qexists_tac ‘fd’
    \\ xsimpl \\ rw []
    \\ rw [fsFFIPropsTheory.forwardFD_o]
    \\ qexists_tac ‘k+x’ \\ xsimpl)
  \\ gvs [std_preludeTheory.OPTION_TYPE_def]
  \\ xmatch
  \\ xapp
QED

Theorem STDIO_ADELKEY:
  hasFreeFD fs ⇒
  STDIO (forwardFD (openFileFS s fs ReadMode 0) (nextFD fs) k with
   infds updated_by ADELKEY (nextFD fs)) ==>> STDIO fs * GC
Proof
  rw []
  \\ ‘nextFD fs ≤ fs.maxFD’ by (imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs [])
  \\ fs [fsFFIPropsTheory.forwardFD_ADELKEY_same]
  \\ fs [fsFFIPropsTheory.openFileFS_ADELKEY_nextFD]
  \\ xsimpl
QED

Theorem open_option_NONE:
  OPTION_TYPE b NONE fnv ∧
  stdin_content fs = SOME text ⇒
  app (p:'ffi ffi_proj) TextIO_open_option_v [fnv]
    (STDIO fs)
    (POSTv retv. SEP_EXISTS is f.
       STDIO fs * INSTREAM_STR 0 is text fs *
       & (OPTION_TYPE (PAIR_TYPE (λx v. v = is) (λx v. v = f)) (SOME ((),())) retv ∧
          sub_spec_none f p is))
Proof
  rpt strip_tac \\ fs []
  \\ gvs [std_preludeTheory.OPTION_TYPE_def]
  \\ xcf_with_def TextIO_open_option_v_def
  \\ xmatch
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ xlet_auto_spec (SOME openStdIn_spec_str)
  THEN1 xsimpl
  \\ xfun_spec `f` ‘sub_spec_none f p is’
  THEN1
   (rw [sub_spec_none_def] \\ first_x_assum irule
    \\ gvs [UNIT_TYPE_def]
    \\ xmatch
    \\ xapp_spec consume_rest_spec)
  \\ xlet_auto
  THEN1 (xcon \\ xsimpl)
  \\ gvs []
  \\ xcon
  \\ xsimpl
  \\ gvs [std_preludeTheory.OPTION_TYPE_def,PAIR_TYPE_def]
  \\ xsimpl
QED

Theorem inFS_fname_file_content_SOME:
  inFS_fname fs fname ∧ consistentFS fs ⇒
  ∃s. file_content fs fname = SOME s
Proof
  rpt strip_tac
  \\ drule_all inFS_fname_ALOOKUP_EXISTS \\ rpt strip_tac
  \\ simp [file_content_def]
QED

Theorem inputAllTokensFrom_SOME:
  CHAR c0 c0v ∧
  OPTION_TYPE FILENAME (SOME fname) fnamev ∧ hasFreeFD fs ∧
  (CHAR --> BOOL) f fv ∧ (STRING_TYPE --> (a:'a->v->bool)) g gv ∧ f c0
  ⇒
  app (p:'ffi ffi_proj) TextIO_inputAllTokensFrom_v
    [c0v; fnamev; fv; gv]
    (STDIO fs)
    (POSTv sv. &OPTION_TYPE (LIST_TYPE (LIST_TYPE a))
           (if inFS_fname fs fname then
              SOME(MAP (MAP g o tokens f) (all_lines_file_gen c0 fs fname))
            else NONE) sv * STDIO fs)
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_inputAllTokensFrom_v_def
  (* TODO This should probably be part of automation *)
  \\ reverse (Cases_on ‘consistentFS fs’)
  THEN1
   (fs [STDIO_def,IOFS_def,wfFS_def] \\ xpull
    \\ fs [fsFFIPropsTheory.consistentFS_def]
    \\ res_tac \\ fs [])
  \\ reverse (Cases_on ‘STD_streams fs’)
  THEN1 (fs [STDIO_def] \\ xpull)
  \\ reverse $ Cases_on ‘inFS_fname fs fname’ \\ simp []
  >-
   (xlet ‘POSTv sv. &OPTION_TYPE _ NONE sv * STDIO fs’
    >-
     (xapp_spec open_option_SOME_fail \\ fs []
      \\ qpat_x_assum ‘¬inFS_fname _ _’ $ irule_at Any \\ fs []
      \\ fs [std_preludeTheory.OPTION_TYPE_def]
      \\ xsimpl)
    \\ fs [std_preludeTheory.OPTION_TYPE_def]
    \\ xmatch \\ xcon \\ xsimpl)
  \\ drule_all inFS_fname_file_content_SOME \\ strip_tac
  \\ drule_all_then assume_tac all_lines_file_gen_lines_of_gen
  \\ drule_all open_option_SOME \\ rpt strip_tac
  \\ xlet_auto >-
   (xsimpl \\ rpt strip_tac
    \\ first_assum $ irule_at (Pos hd)
    \\ simp [] \\ xsimpl)
  \\ gvs [std_preludeTheory.OPTION_TYPE_def, PAIR_TYPE_def]
  \\ xmatch
  \\ reverse $ xhandle
       ‘POSTv sv. STDIO fs *
          &(OPTION_TYPE (LIST_TYPE (LIST_TYPE a))
            (SOME(MAP (MAP g o tokens f) (all_lines_file_gen c0 fs fname)))) sv’
  >- (fs [std_preludeTheory.OPTION_TYPE_def] \\ xsimpl)
  \\ qabbrev_tac ‘fs₁ = openFileFS fname fs ReadMode 0’
  \\ qabbrev_tac ‘fd₁ = nextFD fs’
  \\ xlet
     ‘POSTv v.
          STDIO (fastForwardFD fs₁ fd₁) *
          INSTREAM_LINES c0 fd₁ is [] (fastForwardFD fs₁ fd₁) *
          &LIST_TYPE (LIST_TYPE a)
           (MAP (MAP g o tokens f) (all_lines_file_gen c0 fs fname)) v’
  >-
   (xapp \\ ntac 4 $ first_assum $ irule_at (Pos hd) \\ xsimpl
    \\ qexistsl [‘all_lines_file_gen c0 fs fname’, ‘fs₁’, ‘fd₁’, ‘emp’]
    \\ conj_tac
    >- (simp [INSTREAM_LINES_def] \\ xsimpl \\ qexists ‘s’ \\ xsimpl)
    \\ xsimpl)
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ gvs [sub_spec_def]
  \\ xlet ‘POSTv u.
             &UNIT_TYPE () u *
             STDIO (fs₁ with infds updated_by ADELKEY fd₁)’
  >-
   (xapp \\ qexistsl [‘emp’, ‘[]’, ‘fastForwardFD fs₁ fd₁’]
    \\ simp [INSTREAM_LINES_def, lines_of_gen_def, implode_def] \\ xsimpl
    \\ unabbrev_all_tac \\ simp []
    \\ irule_at Any validFileFD_nextFD \\ simp []
    \\ drule_then assume_tac STD_streams_nextFD \\ simp []
    \\ irule nextFD_leX \\ simp [])
  \\ xcon
  \\ simp [std_preludeTheory.OPTION_TYPE_def] \\ xsimpl
  \\ unabbrev_all_tac
  \\ DEP_REWRITE_TAC [openFileFS_ADELKEY_nextFD] \\ xsimpl
  \\ irule nextFD_leX \\ simp []
QED

Theorem fs_with_infds_updated_by:
  fs with infds updated_by AFUPDKEY k f =
  fs with infds := AFUPDKEY k f fs.infds
Proof
  gvs [K_DEF, IO_fs_component_equality]
QED

(* TODO Can we formulate this generally and stuff it into automation? *)
Theorem STDIO_INSTREAM_STR_fastForwardFD_forwardFD:
  ∃k. STDIO (fastForwardFD fs 0) *
      INSTREAM_STR 0 is rest (fastForwardFD fs 0) ==>>
      STDIO (forwardFD fs 0 k) *
      INSTREAM_STR 0 is rest (forwardFD fs 0 k)
Proof
  simp [fastForwardFD_def]
  \\ Cases_on ‘ALOOKUP fs.infds 0’ \\ simp [the_def]
  >- (qexists ‘0’ \\ xsimpl)
  \\ rename [‘ALOOKUP _ _ = SOME x’]
  \\ namedCases_on ‘x’ ["ino md off"] \\ simp []
  \\ Cases_on ‘ALOOKUP fs.inode_tbl ino’ \\ simp [the_def]
  >- (qexists ‘0’ \\ xsimpl)
  \\ rename [‘ALOOKUP _.inode_tbl _ = SOME x’]
  \\ simp [forwardFD_def, fs_with_infds_updated_by]
  \\ Cases_on ‘STRLEN x < off’
  >-
   (qexists ‘0’
    \\ qmatch_goalsub_abbrev_tac
         ‘STDIO (fs with infds := infds₁) * _ ==>>
          STDIO (fs with infds := infds₂) * _ ’
    \\ ‘infds₁ = infds₂’ by
      (unabbrev_all_tac \\ irule AFUPDKEY_eq \\ simp [MAX_DEF])
    \\ xsimpl)
  \\ qexists ‘STRLEN x - off’
  \\ qmatch_goalsub_abbrev_tac
       ‘STDIO (fs with infds := infds₁) * _ ==>>
        STDIO (fs with infds := infds₂) * _ ’
  \\ ‘infds₁ = infds₂’ by
    (unabbrev_all_tac \\ irule AFUPDKEY_eq \\ simp [MAX_DEF])
  \\ xsimpl
QED

Theorem inputAllTokensFrom_NONE:
  CHAR c0 c0v ∧
  OPTION_TYPE FILENAME NONE fnamev ∧ stdin_content fs = SOME text ∧
  (CHAR --> BOOL) f fv ∧ (STRING_TYPE --> (a:'a->v->bool)) g gv ∧ f c0
  ⇒
  app (p:'ffi ffi_proj) TextIO_inputAllTokensFrom_v
    [c0v; fnamev; fv; gv]
    (STDIO fs)
    (POSTv sv.
       STDIO (fastForwardFD fs 0) *
       &OPTION_TYPE (LIST_TYPE (LIST_TYPE a))
         (SOME(MAP (MAP g o tokens f) (lines_of_gen c0 (implode text)))) sv)
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_inputAllTokensFrom_v_def
  \\ xlet
       ‘POSTv retv. SEP_EXISTS is f.
          STDIO fs * INSTREAM_STR 0 is text fs *
          &(OPTION_TYPE (PAIR_TYPE (λx v. v = is) (λx v. v = f))
              (SOME ((),())) retv ∧ sub_spec_none f p is)’
  (* ensures instantiation of type variables in open_option_NONE *)
  >- (drule_all open_option_NONE \\ strip_tac \\ xapp)
  \\ fs [std_preludeTheory.OPTION_TYPE_def, PAIR_TYPE_def]
  \\ xmatch
  \\ reverse $ xhandle
       ‘POSTv sv. STDIO (fastForwardFD fs 0) *
          &(OPTION_TYPE (LIST_TYPE (LIST_TYPE a))
            (SOME(MAP (MAP g o tokens f) (lines_of_gen c0 (implode text))))) sv’
  >- (fs [std_preludeTheory.OPTION_TYPE_def] \\ xsimpl)
  \\ xlet
     ‘POSTv v.
          STDIO (fastForwardFD fs 0) *
          INSTREAM_LINES c0 0 is [] (fastForwardFD fs 0) *
          &LIST_TYPE (LIST_TYPE a)
           (MAP (MAP g o tokens f) (lines_of_gen c0 (implode text))) v’
  >-
   (xapp \\ ntac 4 $ first_assum $ irule_at (Pos hd) \\ xsimpl
    \\ qexistsl [‘lines_of_gen c0 (implode text)’, ‘fs’, ‘0’, ‘emp’]
    \\ conj_tac
    >- (simp [INSTREAM_LINES_def] \\ xsimpl \\ qexists ‘text’ \\ xsimpl)
    \\ xsimpl)
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ fs [sub_spec_none_def]
  \\ simp [INSTREAM_LINES_def] \\ xpull
  \\ xlet ‘POSTv u. STDIO (fastForwardFD fs 0)’
  >-
   (xapp
    \\ qrefinel [‘emp’, ‘rest’, ‘_’, ‘fs’] \\ xsimpl
    \\ metis_tac [STDIO_INSTREAM_STR_fastForwardFD_forwardFD])
  \\ xcon \\ xsimpl
  \\ simp [std_preludeTheory.OPTION_TYPE_def]
QED

Theorem inputLine_spec_lines:
  CHAR c0 c0v ⇒
  app (p:'ffi ffi_proj) TextIO_inputLine_v [c0v; is]
     (STDIO fs * INSTREAM_LINES c0 fd is lines fs)
     (POSTv v.
       SEP_EXISTS k.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES c0 fd is (TL lines) (forwardFD fs fd k) *
         & (OPTION_TYPE STRING_TYPE (oHD lines) v))
Proof
  strip_tac \\ fs [INSTREAM_LINES_def] \\ xpull
  \\ xapp_spec inputLine_spec_STR \\ rveq
  \\ strip_assume_tac (Q.SPEC ‘rest’ split_exists)
  \\ first_assum (irule_at Any)
  \\ first_assum (irule_at Any)
  \\ qexists_tac`text`
  \\ simp[]
  \\ qexists_tac ‘fs’
  \\ qexists_tac ‘fd’
  \\ xsimpl \\ fs [] \\ rpt strip_tac
  \\ qexists_tac ‘x’ \\ qexists_tac ‘TL text’ \\ xsimpl
  \\ reverse (Cases_on ‘to_read = "" ==> text <> ""’) \\ fs []
  THEN1 (EVAL_TAC \\ fs [std_preludeTheory.OPTION_TYPE_def])
  \\ Cases_on ‘text = ""’ \\ fs []
  \\ fs [lines_of_gen_def]
  THEN1
   (‘~EXISTS ($= c0) to_read’ by fs [EXISTS_MEM,EVERY_MEM]
    \\ drule splitlines_at_not_exists2 \\ fs []
    \\ fs [strcat_def,concat_def,implode_def,str_def]
    \\ Cases_on ‘to_read’ \\ fs [])
  \\ Cases_on ‘to_read = []’ \\ fs []
  THEN1
   (Cases_on ‘text’ \\ fs [] \\ fs [splitlines_at_hd_c0]
    \\ fs [strcat_def,concat_def,implode_def,str_def])
  \\ ‘EXISTS ($= c0) rest’ by (fs [] \\ Cases_on ‘text’ \\ fs [])
  \\ drule splitlines_at_takeUntil_exists2 \\ fs []
  \\ ‘takeUntil ($= c0) (STRCAT to_read text) = to_read’ by
   (‘~EXISTS ($= c0) to_read’ by fs [EXISTS_MEM,EVERY_MEM]
    \\ drule takeUntil_append_not_exists_l \\ fs []
    \\ Cases_on ‘text’ \\ fs [] \\ EVAL_TAC)
  \\ ‘DROP (SUC (STRLEN to_read)) (STRCAT to_read text) = TL text’ by
   (Cases_on ‘text’ \\ fs []
    \\ qmatch_goalsub_abbrev_tac ‘DROP k (xs ++ ys)’
    \\ qsuff_tac ‘k = LENGTH xs’ \\ fs [DROP_LENGTH_APPEND]
    \\ unabbrev_all_tac \\ fs [])
  \\ fs [] \\ Cases_on ‘to_read’ \\ fs [strcat_def,concat_def,implode_def,str_def]
QED

Theorem inputLines_aux_spec:
  !lines acc accv fs.
    CHAR c0 c0v ∧
    LIST_TYPE STRING_TYPE acc accv ==>
    app (p:'ffi ffi_proj) TextIO_inputLines_aux_v
     [c0v; is; accv]
     (STDIO fs * INSTREAM_LINES c0 fd is lines fs)
       (POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES c0 fd is [] (forwardFD fs fd k) *
                & LIST_TYPE STRING_TYPE (REVERSE acc ++ lines) v)
Proof
  gen_tac \\ completeInduct_on `LENGTH lines`
  \\ rpt strip_tac
  \\ xcf_with_def TextIO_inputLines_aux_v_def
  \\ rveq \\ fs [PULL_FORALL]
  \\ xlet `POSTv v.
       SEP_EXISTS k.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES c0 fd is (TL lines) (forwardFD fs fd k) *
         & (OPTION_TYPE STRING_TYPE (oHD lines) v)`
  THEN1 (
    xapp_spec inputLine_spec_lines \\ gvs[])
  \\ Cases_on `lines` \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq
  \\ xmatch \\ fs []
  THEN1
   (xapp_spec (ListProgTheory.reverse_v_thm |> GEN_ALL |> Q.ISPEC ‘STRING_TYPE’)
    \\ asm_exists_tac \\ fs [] \\ xsimpl \\ rw []
    \\ qexists_tac ‘k’ \\ xsimpl)
  \\ xlet_auto THEN1 (xcon \\ xsimpl \\ fs [])
  \\ rveq \\ fs []
  \\ xapp
  \\ qexists_tac `emp` \\ xsimpl
  \\ qexists_tac `t` \\ qexists_tac `forwardFD fs fd k` \\ qexists_tac `h::acc`
  \\ fs [LIST_TYPE_def] \\ xsimpl \\ rw []
  \\ qexists_tac `x+k`
  \\ fs [forwardFD_o] \\ xsimpl
  \\ pop_assum mp_tac
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
QED

Theorem inputLines_spec:
   CHAR c0 c0v ==>
   app (p:'ffi ffi_proj) TextIO_inputLines_v
     [c0v; is]
     (STDIO fs * INSTREAM_LINES c0 fd is lines fs)
       (POSTv v.
         STDIO (fastForwardFD fs fd) *
         INSTREAM_LINES c0 fd is [] (fastForwardFD fs fd) *
         & LIST_TYPE STRING_TYPE lines v)
Proof
  rw []
  \\ xcf_with_def TextIO_inputLines_v_def
  \\ xlet_auto
  THEN1 (xcon \\ xsimpl \\ fs [])
  \\ xapp_spec inputLines_aux_spec
  \\ qexists_tac `emp`
  \\ qexists_tac `lines`
  \\ qexists_tac `fs`
  \\ qexists_tac `fd`
  \\ qexists_tac `c0`
  \\ qexists_tac `[]`
  \\ xsimpl
  \\ conj_tac >- fs [LIST_TYPE_def]
  \\ fs [INSTREAM_LINES_def,INSTREAM_STR_def]
  \\ xsimpl \\ rw[] \\ gs[lines_of_gen_def,implode_def] \\ rveq
  \\ qmatch_assum_rename_tac ‘get_file_content _ _ = SOME (c,off)’
  \\ gs[] \\ rveq \\ simp [GSYM PULL_EXISTS]
  \\ conj_tac
  >- (qexists_tac ‘c’ \\ gs[get_file_content_def,fastForwardFD_def]
      \\ PairCases_on ‘x'’
      \\ qmatch_assum_rename_tac ‘ALOOKUP _ _ = SOME (ino,mode,off')’
      \\ gs[] \\ simp[miscTheory.the_def,AFUPDKEY_ALOOKUP,MAX_DEF])
  \\ conj_tac
  >- (gs[get_mode_def,fastForwardFD_def,get_file_content_def]
      \\ PairCases_on ‘x'’
      \\ qmatch_assum_rename_tac ‘ALOOKUP _ _ = SOME (ino,mode,off')’
      \\ gs[] \\ simp[miscTheory.the_def,AFUPDKEY_ALOOKUP])
  \\ xsimpl \\ simp[fastForwardFD_eq_forwardFD] \\ xsimpl
QED

Theorem inputLinesFile_spec:
   CHAR c0 c0v ∧
   FILENAME f fv /\ hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) TextIO_inputLinesFile_v
     [c0v ; fv]
     (STDIO fs)
     (POSTv sv. &OPTION_TYPE (LIST_TYPE STRING_TYPE)
            (if inFS_fname fs f then
               SOME(all_lines_file_gen c0 fs f)
             else NONE) sv
             * STDIO fs)
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_inputLinesFile_v_def
  \\ reverse (Cases_on `STD_streams fs`)
  >- (fs [STDIO_def] \\ xpull)
  \\ reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def] \\ xpull \\ metis_tac[])
  \\ reverse IF_CASES_TAC
  >- (
    xhandle`POSTe ev. &BadFileName_exn ev * STDIO fs`
    >- (xlet_auto_spec (SOME openIn_STDIO_spec) \\ xsimpl)
    \\ fs[BadFileName_exn_def] \\ xcases \\ rw[]
    \\ xcon \\ xsimpl \\ fs [std_preludeTheory.OPTION_TYPE_def])
  \\ qmatch_goalsub_abbrev_tac`$POSTv Qval`
  \\ xhandle`$POSTv Qval` \\ xsimpl
  \\ xlet_auto_spec (SOME openIn_spec_lines) \\ xsimpl
  \\ unabbrev_all_tac
  \\ qabbrev_tac `fs1 = openFileFS f fs ReadMode 0`
  \\ xlet `(POSTv v.
                STDIO (fastForwardFD fs1 (nextFD fs)) *
                INSTREAM_LINES c0 (nextFD fs) is [] (fastForwardFD fs1 (nextFD fs)) *
                & LIST_TYPE STRING_TYPE (all_lines_file_gen c0 fs f) v)`
  THEN1
   (xapp_spec inputLines_spec
    \\ qexists_tac `emp`
    \\ qexists_tac `all_lines_file_gen c0 fs f`
    \\ qexists_tac `fs1`
    \\ qexists_tac `nextFD fs`
    \\ qexists_tac `c0`
    \\ xsimpl \\ rw [])
  \\ xlet `POSTv v. STDIO fs`
  THEN1
   (xapp_spec closeIn_spec_lines
    \\ qexists_tac `emp`
    \\ qexists_tac `[]`
    \\ qexists_tac `fastForwardFD fs1 (nextFD fs)`
    \\ qexists_tac `nextFD fs`
    \\ qexists_tac `c0`
    \\ conj_tac THEN1
     (fs [forwardFD_def,Abbr`fs1`]
      \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
      \\ imp_res_tac fsFFIPropsTheory.STD_streams_nextFD \\ fs [])
    \\ `validFileFD (nextFD fs) (fastForwardFD fs1 (nextFD fs)).infds` by
      (simp[validFileFD_fastForwardFD]>> simp[Abbr`fs1`]
       \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
       \\ match_mp_tac validFileFD_nextFD \\ fs [])
    \\ xsimpl \\ rw [Abbr`fs1`,fsFFIPropsTheory.forwardFD_ADELKEY_same]
    \\ imp_res_tac LESS_IMP_LESS_OR_EQ
    \\ imp_res_tac fsFFIPropsTheory.nextFD_leX \\ fs []
    \\ drule fsFFIPropsTheory.openFileFS_ADELKEY_nextFD
    \\ fs [] \\ xsimpl)
  \\ xcon \\ xsimpl
  \\ fs [std_preludeTheory.OPTION_TYPE_def]
QED

Theorem inputLinesStdIn_spec:
  CHAR c0 c0v ∧
  stdin_content fs = SOME text
  ⇒
   app (p:'ffi ffi_proj) TextIO_inputLinesStdIn_v
     [c0v]
     (STDIO fs)
     (POSTv sv.
       & LIST_TYPE STRING_TYPE (lines_of_gen c0 (implode text)) sv
       * STDIO (fastForwardFD fs 0))
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_inputLinesStdIn_v_def
  \\ reverse (Cases_on `STD_streams fs`)
  >- (fs [STDIO_def] \\ xpull)
  \\ reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def] \\ xpull \\ metis_tac[])
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto_spec (SOME openStdIn_spec_lines) \\ xsimpl
  \\ xapp_spec inputLines_spec
  \\ qexists_tac `emp`
  \\ qexists_tac `lines_of_gen c0 (implode text)`
  \\ qexists_tac `fs`
  \\ qexists_tac `0`
  \\ qexists_tac `c0`
  \\ xsimpl \\ rw [implode_def]
QED

Theorem extend_array_spec:
  ∀arrv arr.
  app (p:'ffi ffi_proj) TextIO_extend_array_v [arrv] (W8ARRAY arrv arr)
        (POSTv v. W8ARRAY v (arr ++ (REPLICATE (LENGTH arr) 0w)))
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_extend_array_v_def
  \\ ntac 5 (xlet_auto >- xsimpl)
  \\ xret \\ xsimpl
  \\ simp[DROP_REPLICATE]
QED

Theorem inputAll_spec:
  get_file_content fs fd = SOME (content,pos) ⇒
  get_mode fs fd = SOME ReadMode ⇒
  app (p:'ffi ffi_proj) TextIO_inputAll_v [is]
    (STDIO fs * INSTREAM_BUFFERED_FD bactive fd is)
    (POSTv v.
       &STRING_TYPE (implode (DROP pos content)) v *
       STDIO (fastForwardFD fs fd))
Proof
  rpt strip_tac \\
  xcf_with_def TextIO_inputAll_v_def \\
  simp[INSTREAM_BUFFERED_FD_def] \\ xpull \\ xmatch \\
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
      xif \\ gvs [] \\
      xlet_auto >- xsimpl \\
      xlet_auto_spec(SOME raw_input_spec)
      >- xsimpl \\
      xlet_auto >- xsimpl \\
      xif \\ instantiate \\
      xapp \\
      simp[DROP_LENGTH_TOO_LONG,insert_atI_NIL] \\
      xsimpl \\ instantiate \\
      simp[STRING_TYPE_def] \\
      simp[MAX_DEF] \\
      simp[fsupdate_unchanged] \\
      simp[implode_def] \\
      xsimpl )
    \\ xapp \\ xsimpl
    \\ simp[DROP_LENGTH_TOO_LONG,implode_def]
    \\ simp[fastForwardFD_0]
    \\ xsimpl
    \\ fs [instream_buffered_inv_def]
    \\ CCONTR_TAC \\ fs [])
  \\ qabbrev_tac`arrmax = SUC (MAX (256**2) (2 * (LENGTH content - pos)))`
  \\ reverse (xfun_spec `inputAll_aux`
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
        STDIO (fastForwardFD fs fd))`)
  >- (
  xapp
  \\ qpat_x_assum ‘get_mode _ _ = _’ $ irule_at Any \\ xsimpl
  \\ fs [instream_buffered_inv_def]
  \\ conj_tac >- (CCONTR_TAC \\ fs [])
  \\ fs [Abbr ‘arrmax’]
  \\ intLib.COOPER_TAC) \\
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
  reverse xif \\ fs[]
  >- (
    xlet_auto >- xsimpl
    \\ xapp
    \\ simp[Abbr`arrmax`]
    \\ xsimpl
    \\ instantiate
    \\ simp[LEX_DEF,TAKE_APPEND]
    \\ xsimpl
    \\ fs[MAX_DEF]
    \\ CCONTR_TAC \\ fs[])
  \\ xlet_auto >- xsimpl
  \\ xlet_auto_spec(SOME raw_input_spec) >- xsimpl
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
    \\ fs[IO_fs_component_equality,AFUPDKEY_unchanged,AFUPDKEY_eq] )
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
  \\ rw[ORD_BOUND,CHR_ORD]
QED

Theorem fold_chars_loop_thm:
  ∀is a f fv s y yv fs fd.
    (CHAR --> a --> a) f fv ∧ a y yv ⇒
    app (p:'ffi ffi_proj) TextIO_fold_chars_loop_v [fv; is; yv]
      (STDIO fs * INSTREAM_STR fd is s fs)
      (POSTv retv. SEP_EXISTS k.
         STDIO (forwardFD fs fd k) *
         INSTREAM_STR fd is [] (forwardFD fs fd k) *
         &a (mllist$foldl f y s) retv)
Proof
  ntac 4 strip_tac
  \\ Induct
  THEN1
   (rw []
    \\ xcf_with_def TextIO_fold_chars_loop_v_def
    \\ xlet ‘(POSTv chv. SEP_EXISTS k.
          STDIO (forwardFD fs fd k) *
          INSTREAM_STR fd is [] (forwardFD fs fd k) *
          &OPTION_TYPE CHAR NONE chv)’
    THEN1
     (xapp_spec (input1_spec_str |> Q.INST [‘s’|->‘[]’] )
      \\ qexists_tac ‘emp’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’
      \\ xsimpl \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl)
    \\ gvs [std_preludeTheory.OPTION_TYPE_def]
    \\ xmatch \\ xvar
    \\ fs [mllistTheory.foldl_def]
    \\ xsimpl \\ qexists_tac ‘k’ \\ xsimpl)
  \\ rw[]
  \\ xcf_with_def TextIO_fold_chars_loop_v_def
  \\ xlet ‘(POSTv chv. SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_STR fd is s (forwardFD fs fd k) *
            &OPTION_TYPE CHAR (SOME h) chv)’
  THEN1
   (xapp_spec (input1_spec_str |> Q.INST [‘s’|->‘STRING h s’] )
    \\ qexists_tac ‘emp’
    \\ qexists_tac ‘s’
    \\ qexists_tac ‘h’
    \\ qexists_tac ‘fs’
    \\ qexists_tac ‘fd’
    \\ xsimpl \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl)
  \\ gvs [std_preludeTheory.OPTION_TYPE_def]
  \\ xmatch
  \\ xlet_auto THEN1 xsimpl
  \\ first_x_assum drule \\ strip_tac
  \\ xapp
  \\ qexists_tac ‘emp’
  \\ qexists_tac ‘(forwardFD fs fd k)’
  \\ qexists_tac ‘fd’
  \\ xsimpl
  \\ rw []
  \\ qexists_tac ‘x+k’
  \\ fs [fsFFIPropsTheory.forwardFD_o]
  \\ xsimpl \\ fs [mllistTheory.foldl_def]
QED

Theorem fold_lines_loop_thm:
  ∀is a f fv s y yv fs fd c0 c0v.
    CHAR c0 c0v ∧
    (STRING_TYPE --> a --> a) f fv ∧ a y yv ⇒
    app (p:'ffi ffi_proj) TextIO_fold_lines_loop_v [c0v; fv; is; yv]
      (STDIO fs * INSTREAM_LINES c0 fd is s fs)
      (POSTv retv. SEP_EXISTS k.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES c0 fd is [] (forwardFD fs fd k) *
         &a (mllist$foldl f y s) retv)
Proof
  ntac 4 strip_tac
  \\ Induct
  THEN1
   (rw []
    \\ xcf_with_def TextIO_fold_lines_loop_v_def
    \\ xlet ‘(POSTv chv. SEP_EXISTS k.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES c0 fd is [] (forwardFD fs fd k) *
          &OPTION_TYPE STRING_TYPE NONE chv)’
    THEN1
     (xapp_spec (inputLine_spec_lines |> Q.INST [‘lines’|->‘[]’] )
      \\ qexists_tac ‘emp’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’
      \\ qexists_tac ‘c0’
      \\ xsimpl \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl)
    \\ gvs [std_preludeTheory.OPTION_TYPE_def]
    \\ xmatch \\ xvar
    \\ fs [mllistTheory.foldl_def]
    \\ xsimpl \\ qexists_tac ‘k’ \\ xsimpl)
  \\ rw[]
  \\ xcf_with_def TextIO_fold_lines_loop_v_def
  \\ xlet ‘(POSTv chv. SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES c0 fd is s (forwardFD fs fd k) *
            &OPTION_TYPE STRING_TYPE (SOME h) chv)’
  THEN1
   (xapp_spec (inputLine_spec_lines |> Q.INST [‘lines’|->‘h::s’] )
    \\ qexists_tac ‘emp’
    \\ qexists_tac ‘s’
    \\ qexists_tac ‘h’
    \\ qexists_tac ‘fs’
    \\ qexists_tac ‘fd’
    \\ qexists_tac ‘c0’
    \\ xsimpl \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl)
  \\ gvs [std_preludeTheory.OPTION_TYPE_def]
  \\ xmatch
  \\ xlet_auto THEN1 xsimpl
  \\ first_x_assum drule \\ strip_tac
  \\ xapp
  \\ qexists_tac ‘emp’
  \\ asm_exists_tac
  \\ qexists_tac ‘(forwardFD fs fd k)’
  \\ qexists_tac ‘fd’
  \\ xsimpl
  \\ rw []
  \\ qexists_tac ‘x+k’
  \\ fs [fsFFIPropsTheory.forwardFD_o]
  \\ xsimpl \\ fs [mllistTheory.foldl_def]
QED

Theorem foldChars_SOME:
  (CHAR --> a --> a) f fv ∧ a x xv ∧
  OPTION_TYPE FILENAME (SOME s) fnv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) TextIO_foldChars_v [fv; xv; fnv]
    (STDIO fs)
    (POSTv retv. STDIO fs *
                 & (OPTION_TYPE a
                      (OPTION_MAP (foldl f x) (file_content fs s))
                      retv))
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_foldChars_v_def
  \\ reverse (Cases_on ‘STD_streams fs’)
  THEN1 (fs [STDIO_def] \\ xpull)
  \\ reverse (Cases_on ‘consistentFS fs’)
  THEN1
    (fs [STDIO_def,IOFS_def,wfFS_def] \\ xpull
     \\ fs [fsFFIPropsTheory.consistentFS_def]
     \\ res_tac \\ fs [])
  \\ Cases_on ‘file_content fs s’ \\ fs []
  THEN1
   (xlet ‘POSTv retv. STDIO fs * &OPTION_TYPE a NONE retv’
    THEN1
     (xapp_spec open_option_SOME_fail \\ fs []
      \\ first_assum $ irule_at Any \\ fs []
      \\ fs [file_content_def,AllCaseEqs(),inFS_fname_def]
      \\ fs [consistentFS_def]
      \\ res_tac
      \\ fs [MEM_MAP,ALOOKUP_NONE]
      \\ metis_tac [])
    \\ gvs [std_preludeTheory.OPTION_TYPE_def]
    \\ xmatch \\ xcon \\ xsimpl)
  \\ full_simp_tac std_ss []
  \\ rename [‘file_content fs s = SOME text’]
  \\ ‘inFS_fname fs s’ by fs [inFS_fname_def,file_content_def,AllCaseEqs()]
  \\ drule_all (SIMP_RULE std_ss [] open_option_SOME)
  \\ disch_then (assume_tac o SPEC_ALL)
  \\ xlet_auto
  THEN1
   (xsimpl \\ gvs [std_preludeTheory.OPTION_TYPE_def,PAIR_TYPE_def] \\ xsimpl)
  \\ gvs [std_preludeTheory.OPTION_TYPE_def,PAIR_TYPE_def]
  \\ xmatch
  \\ reverse (xhandle
    ‘(POSTv retv. STDIO fs *
                 & (OPTION_TYPE a (SOME (mllist$foldl f x text)) retv))’)
  THEN1 (xsimpl \\ rw [] \\ gvs [std_preludeTheory.OPTION_TYPE_def,PAIR_TYPE_def])
  \\ drule_all fold_chars_loop_thm
  \\ qabbrev_tac ‘fs1 = openFileFS s fs ReadMode 0’
  \\ disch_then (qspecl_then [‘p’,‘is’,‘text’,‘fs1’,‘nextFD fs’] assume_tac)
  \\ xlet_auto
  THEN1 (xsimpl  \\ rw [] \\ qexists_tac ‘x'’ \\ xsimpl)
  \\ xlet_auto
  THEN1 (xcon \\ xsimpl)
  \\ fs [sub_spec_def]
  \\ last_x_assum drule
  \\ disch_then (qspecl_then [‘forwardFD fs1 (nextFD fs) k’,‘""’] mp_tac)
  \\ impl_tac
  THEN1
   (fs [Abbr‘fs1’,validFileFD_forwardFD]
    \\ irule_at Any validFileFD_nextFD \\ fs []
    \\ imp_res_tac LESS_IMP_LESS_OR_EQ
    \\ imp_res_tac fsFFIPropsTheory.nextFD_leX \\ fs []
    \\ imp_res_tac fsFFIPropsTheory.STD_streams_nextFD \\ fs [])
  \\ strip_tac
  \\ xlet_auto
  THEN1 (xsimpl \\ gvs [UNIT_TYPE_def])
  \\ xcon \\ xsimpl
  \\ gvs [std_preludeTheory.OPTION_TYPE_def,PAIR_TYPE_def]
  \\ unabbrev_all_tac
  \\ irule STDIO_ADELKEY \\ fs []
QED

Theorem foldChars_NONE:
  (CHAR --> a --> a) f fv ∧ a x xv ∧
  OPTION_TYPE FILENAME NONE fnv ∧
  stdin_content fs = SOME text
  ⇒
  app (p:'ffi ffi_proj) TextIO_foldChars_v [fv; xv; fnv]
    (STDIO fs)
    (POSTv retv. STDIO (fastForwardFD fs 0) *
                 & (OPTION_TYPE a (SOME (foldl f x text)) retv))
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_foldChars_v_def
  \\ drule_all (SIMP_RULE std_ss [] open_option_NONE)
  \\ disch_then (assume_tac o SPEC_ALL)
  \\ xlet_auto
  THEN1
   (xsimpl \\ gvs [std_preludeTheory.OPTION_TYPE_def,PAIR_TYPE_def] \\ xsimpl)
  \\ gvs [std_preludeTheory.OPTION_TYPE_def,PAIR_TYPE_def]
  \\ xmatch
  \\ reverse (xhandle
    ‘(POSTv retv. STDIO (fastForwardFD fs 0) *
                 & (OPTION_TYPE a (SOME (mllist$foldl f x text)) retv))’)
  THEN1 (xsimpl \\ rw [] \\ gvs [std_preludeTheory.OPTION_TYPE_def,PAIR_TYPE_def])
  \\ drule_all fold_chars_loop_thm
  \\ disch_then (qspecl_then [‘p’,‘is’,‘text’,‘fs’,‘0’] assume_tac)
  \\ xlet_auto
  THEN1 (xsimpl  \\ rw [] \\ qexists_tac ‘x'’ \\ xsimpl)
  \\ xlet_auto
  THEN1 (xcon \\ xsimpl)
  \\ fs [sub_spec_none_def]
  \\ last_x_assum drule
  \\ disch_then (qspecl_then [‘fs’,‘""’,‘k’] mp_tac)
  \\ strip_tac
  \\ xlet_auto
  THEN1 (qexists_tac ‘emp’ \\ xsimpl)
  \\ xcon \\ xsimpl
  \\ gvs [std_preludeTheory.OPTION_TYPE_def,PAIR_TYPE_def]
QED

Theorem foldLines_SOME:
  CHAR c0 c0v ∧
  (STRING_TYPE --> a --> a) f fv ∧ a x xv ∧
  OPTION_TYPE FILENAME (SOME s) fnv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) TextIO_foldLines_v [c0v; fv; xv; fnv]
    (STDIO fs)
    (POSTv retv. STDIO fs *
                 & (OPTION_TYPE a
                      (OPTION_MAP (foldl f x o lines_of_gen c0 o implode) (file_content fs s))
                      retv))
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_foldLines_v_def
  \\ reverse (Cases_on ‘STD_streams fs’)
  THEN1 (fs [STDIO_def] \\ xpull)
  \\ reverse (Cases_on ‘consistentFS fs’)
  THEN1
    (fs [STDIO_def,IOFS_def,wfFS_def] \\ xpull
     \\ fs [fsFFIPropsTheory.consistentFS_def]
     \\ res_tac \\ fs [])
  \\ Cases_on ‘file_content fs s’ \\ fs []
  THEN1
   (xlet ‘POSTv retv. STDIO fs * &OPTION_TYPE a NONE retv’
    THEN1
     (xapp_spec open_option_SOME_fail \\ fs []
      \\ first_assum $ irule_at Any \\ fs []
      \\ fs [file_content_def,AllCaseEqs(),inFS_fname_def]
      \\ fs [consistentFS_def]
      \\ res_tac
      \\ fs [MEM_MAP,ALOOKUP_NONE]
      \\ metis_tac [])
    \\ gvs [std_preludeTheory.OPTION_TYPE_def]
    \\ xmatch \\ xcon \\ xsimpl)
  \\ full_simp_tac std_ss []
  \\ rename [‘file_content fs s = SOME text’]
  \\ ‘inFS_fname fs s’ by fs [inFS_fname_def,file_content_def,AllCaseEqs()]
  \\ drule_all (SIMP_RULE std_ss [] open_option_SOME)
  \\ disch_then (assume_tac o SPEC_ALL)
  \\ xlet_auto
  THEN1
   (xsimpl \\ gvs [std_preludeTheory.OPTION_TYPE_def,PAIR_TYPE_def] \\ xsimpl)
  \\ gvs [std_preludeTheory.OPTION_TYPE_def,PAIR_TYPE_def]
  \\ xmatch
  \\ reverse (xhandle
    ‘(POSTv retv. STDIO fs *
        & (OPTION_TYPE a (SOME (mllist$foldl f x (lines_of_gen c0 (implode text)))) retv))’)
  THEN1 (xsimpl \\ rw [] \\ gvs [std_preludeTheory.OPTION_TYPE_def,PAIR_TYPE_def])
  \\ drule_all fold_lines_loop_thm
  \\ qabbrev_tac ‘fs1 = openFileFS s fs ReadMode 0’
  \\ disch_then (qspecl_then [‘p’,‘is’,‘lines_of_gen c0 (implode text)’,‘fs1’,‘nextFD fs’]
                   assume_tac)
  \\ fs [INSTREAM_LINES_def,SEP_CLAUSES,app_SEP_EXISTS]
  \\ pop_assum $ qspec_then ‘text’ mp_tac
  \\ fs [SEP_CLAUSES] \\ rw []
  \\ full_simp_tac (std_ss ++ sep_cond_ss) [implode_def]
  \\ fs []
  \\ xlet_auto
  THEN1 (xsimpl  \\ rw [] \\ qexists_tac ‘x'’ \\ xsimpl)
  \\ xlet_auto
  THEN1 (xcon \\ xsimpl)
  \\ fs [sub_spec_def]
  \\ last_x_assum drule
  \\ disch_then (qspecl_then [‘forwardFD fs1 (nextFD fs) k’,‘rest’] mp_tac)
  \\ impl_tac
  THEN1
   (fs [Abbr‘fs1’,validFileFD_forwardFD]
    \\ irule_at Any validFileFD_nextFD \\ fs []
    \\ imp_res_tac LESS_IMP_LESS_OR_EQ
    \\ imp_res_tac fsFFIPropsTheory.nextFD_leX \\ fs []
    \\ imp_res_tac fsFFIPropsTheory.STD_streams_nextFD \\ fs [])
  \\ strip_tac
  \\ xlet_auto
  THEN1 (xsimpl \\ gvs [UNIT_TYPE_def])
  \\ xcon \\ xsimpl
  \\ gvs [std_preludeTheory.OPTION_TYPE_def,PAIR_TYPE_def]
  \\ unabbrev_all_tac
  \\ irule STDIO_ADELKEY \\ fs []
QED

Theorem foldLines_NONE:
  CHAR c0 c0v ∧
  (STRING_TYPE --> a --> a) f fv ∧ a x xv ∧
  OPTION_TYPE FILENAME NONE fnv ∧
  stdin_content fs = SOME text
  ⇒
  app (p:'ffi ffi_proj) TextIO_foldLines_v [c0v; fv; xv; fnv]
    (STDIO fs)
    (POSTv retv. STDIO (fastForwardFD fs 0) *
        & (OPTION_TYPE a (SOME (foldl f x (lines_of_gen c0 (implode text)))) retv))
Proof
  rpt strip_tac
  \\ xcf_with_def TextIO_foldLines_v_def
  \\ drule_all (SIMP_RULE std_ss [] open_option_NONE)
  \\ disch_then (assume_tac o SPEC_ALL)
  \\ xlet_auto
  THEN1
   (xsimpl \\ gvs [std_preludeTheory.OPTION_TYPE_def,PAIR_TYPE_def] \\ xsimpl)
  \\ gvs [std_preludeTheory.OPTION_TYPE_def,PAIR_TYPE_def]
  \\ xmatch
  \\ reverse (xhandle
    ‘(POSTv retv. STDIO (fastForwardFD fs 0) *
        & (OPTION_TYPE a (SOME (mllist$foldl f x (lines_of_gen c0 (implode text)))) retv))’)
  THEN1 (xsimpl \\ rw [] \\ gvs [std_preludeTheory.OPTION_TYPE_def,PAIR_TYPE_def])
  \\ drule_all fold_lines_loop_thm
  \\ disch_then (qspecl_then [‘p’,‘is’,‘lines_of_gen c0 (implode text)’,‘fs’,‘0’] assume_tac)
  \\ fs [INSTREAM_LINES_def,SEP_CLAUSES,app_SEP_EXISTS]
  \\ pop_assum $ qspec_then ‘text’ mp_tac
  \\ full_simp_tac (std_ss ++ sep_cond_ss) [implode_def]
  \\ fs [SEP_CLAUSES] \\ rw []
  \\ xlet_auto
  THEN1 (xsimpl \\ rw [] \\ qexists_tac ‘x'’ \\ xsimpl)
  \\ xlet_auto
  THEN1 (xcon \\ xsimpl)
  \\ fs [sub_spec_none_def]
  \\ last_x_assum drule
  \\ disch_then (qspecl_then [‘fs’,‘rest’,‘k’] mp_tac) \\ simp []
  \\ strip_tac
  \\ xlet_auto
  THEN1 (qexists_tac ‘emp’ \\ xsimpl)
  \\ xcon \\ xsimpl
  \\ gvs [std_preludeTheory.OPTION_TYPE_def,PAIR_TYPE_def]
QED
