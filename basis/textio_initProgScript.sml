open preamble
     ml_translatorTheory ml_translatorLib ml_progLib
     cfTacticsBaseLib cfTacticsLib basisFunctionsLib
     mlstringTheory mlcommandlineProgTheory fsFFITheory fsFFIProofTheory

val _ = new_theory"textio_initProg";
(* filesystem constants and corresponding hprops *)
val _ = translation_extends "mlcommandlineProg";
val _ = ml_prog_update (open_module "TextIO");

val _ = process_topdecs `
  exception BadFileName;
  exception InvalidFD;
  exception EndOfFile
` |> append_prog

(* 258 w8 array *)
val iobuff_e = ``(App Aw8alloc [Lit (IntLit 258); Lit (Word8 0w)])``
val _ = ml_prog_update
          (add_Dlet (derive_eval_thm "iobuff_loc" iobuff_e) "iobuff" [])
val iobuff_loc_def = definition "iobuff_loc_def"
val iobuff_loc = EVAL``iobuff_loc`` |> curry save_thm "iobuff_loc"

val _ = export_rewrites["iobuff_loc"]

val IOFS_iobuff_def = Define`
  IOFS_iobuff =
    SEP_EXISTS v. W8ARRAY iobuff_loc v * cond (LENGTH v = 258) `;

val IOFS_def = Define `
  IOFS fs = IOx fs_ffi_part fs * IOFS_iobuff * &wfFS fs`


val BadFileName_exn_def = Define `
  BadFileName_exn v =
    (v = Conv (SOME ("BadFileName", TypeExn (Long "TextIO" (Short "BadFileName")))) [])`

val InvalidFD_exn_def = Define `
  InvalidFD_exn v =
    (v = Conv (SOME ("InvalidFD", TypeExn (Long "TextIO" (Short "InvalidFD")))) [])`

val EndOfFile_exn_def = Define `
  EndOfFile_exn v =
    (v = Conv (SOME ("EndOfFile", TypeExn (Long "TextIO" (Short "EndOfFile")))) [])`

val FILENAME_def = Define `
  FILENAME s sv =
    (STRING_TYPE s sv ∧
     ¬MEM (CHR 0) (explode s) ∧
     strlen s < 256)
`;

(* stdin, stdout, stderr *)
val stdIn_def = Define`stdIn:word8 = n2w 0`;
val stdOut_def = Define`stdOut:word8 = n2w 1`;
val stdErr_def = Define`stdErr:word8 = n2w 2`;
val _ = next_ml_names := ["stdIn","stdOut","stdErr"];
val r = translate stdIn_def;
val r = translate stdOut_def;
val r = translate stdErr_def;

(* Property ensuring that standard streams are correctly opened *)
val STD_streams_def = Define
`STD_streams fs = ?inp out err.
    (ALOOKUP fs.files (IOStream(strlit "stdout")) = SOME out) ∧
    (ALOOKUP fs.files (IOStream(strlit "stderr")) = SOME err) ∧
    (∀fd off. ALOOKUP fs.infds fd = SOME (IOStream(strlit "stdin"),off) ⇔ fd = 0 ∧ off = inp) ∧
    (∀fd off. ALOOKUP fs.infds fd = SOME (IOStream(strlit "stdout"),off) ⇔ fd = 1 ∧ off = LENGTH out) ∧
    (∀fd off. ALOOKUP fs.infds fd = SOME (IOStream(strlit "stderr"),off) ⇔ fd = 2 ∧ off = LENGTH err)`;

(* "end-user" property *)
(* abstracts away the lazy list and ensure that standard streams are opened on
* their respective standard fds at the right position *)
val STDIO_def = Define`
 STDIO fs = (SEP_EXISTS ll. IOFS (fs with numchars := ll)) *
   &STD_streams fs`

val STD_streams_fsupdate = Q.store_thm("STD_streams_fsupdate",
  `! fs fd k pos c.
   ((fd = 1 \/ fd = 2) ==> LENGTH c = pos) /\
   (*
   (fd >= 3 ==> (FST(THE (ALOOKUP fs.infds fd)) <> IOStream(strlit "stdout") /\
                 FST(THE (ALOOKUP fs.infds fd)) <> IOStream(strlit "stderr"))) /\
   *)
    STD_streams fs ==>
    STD_streams (fsupdate fs fd k pos c)`,
  rw[STD_streams_def,fsupdate_def]
  \\ CASE_TAC \\ fs[] >- metis_tac[]
  \\ CASE_TAC \\ fs[ALIST_FUPDKEY_ALOOKUP]
  \\ qmatch_goalsub_abbrev_tac`out' = SOME _ ∧ (err' = SOME _ ∧ _)`
  \\ qmatch_assum_rename_tac`_ = SOME (fnm,_)`
  \\ map_every qexists_tac[`if fnm = IOStream(strlit"stdin") then pos else inp`,`THE out'`,`THE err'`]
  \\ conj_tac >- rw[Abbr`out'`]
  \\ conj_tac >- rw[Abbr`err'`]
  \\ unabbrev_all_tac
  \\ rw[] \\ fs[] \\ rw[] \\ TOP_CASE_TAC \\ fs[] \\ rw[] \\ rfs[]
  \\ rw[] \\ rfs[PAIR_MAP]
  \\ metis_tac[NOT_SOME_NONE,SOME_11,PAIR,FST]);

val option_case_eq = prove_case_eq_thm{case_def = option_case_def, nchotomy = option_nchotomy}

val STD_streams_openFileFS = Q.store_thm("STD_streams_openFileFS",
  `!fs s k. STD_streams fs ==> STD_streams (openFileFS s fs k)`,
   rw[STD_streams_def,openFileFS_files] >>
   map_every qexists_tac[`inp`,`out`,`err`] >>
   fs[openFileFS_def] >> rpt(CASE_TAC >> fs[]) >>
   fs[openFile_def,IO_fs_component_equality] >>
   qpat_x_assum`_::_ = _`(assume_tac o SYM) \\ fs[] \\
   rw[] \\ metis_tac[ALOOKUP_MEM,nextFD_NOT_MEM,PAIR]);

open cfLetAutoTheory cfLetAutoLib

val UNIQUE_IOFS = Q.store_thm("UNIQUE_IOFS",
`!s. VALID_HEAP s ==> !fs1 fs2 H1 H2. (IOFS fs1 * H1) s /\
                                      (IOFS fs2 * H2) s ==> fs1 = fs2`,
  rw[IOFS_def,cfHeapsBaseTheory.IOx_def, fs_ffi_part_def,
     GSYM STAR_ASSOC,encode_def] >>
  IMP_RES_TAC FRAME_UNIQUE_IO >>
  fs[encode_files_11,encode_fds_11,IO_fs_component_equality]);

val IOFS_FFI_part_hprop = Q.store_thm("IOFS_FFI_part_hprop",
  `FFI_part_hprop (IOFS fs)`,
  rw [IOFS_def,
      cfHeapsBaseTheory.IO_def, cfHeapsBaseTheory.IOx_def,
      fs_ffi_part_def, cfMainTheory.FFI_part_hprop_def,
    set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
    cfHeapsBaseTheory.W8ARRAY_def,IOFS_iobuff_def,
    cfHeapsBaseTheory.cell_def]
  \\ fs[set_sepTheory.one_STAR,STAR_def]
  \\ imp_res_tac SPLIT_SUBSET >> fs[SUBSET_DEF]
  \\ metis_tac[]);

val IOFS_iobuff_HPROP_INJ = Q.store_thm("IOFS_iobuff_HPROP_INJ[hprop_inj]",
`!fs1 fs2. HPROP_INJ (IOFS fs1) (IOFS fs2) (fs2 = fs1)`,
  rw[HPROP_INJ_def, IOFS_def, GSYM STAR_ASSOC, SEP_CLAUSES, SEP_EXISTS_THM,
     HCOND_EXTRACT] >>
  fs[IOFS_def,cfHeapsBaseTheory.IOx_def, fs_ffi_part_def] >>
  EQ_TAC >> rpt DISCH_TAC >> IMP_RES_TAC FRAME_UNIQUE_IO >> fs[]);

val filename_tac = metis_tac[FILENAME_def,EqualityType_NUM_BOOL,EqualityType_def];

val FILENAME_UNICITY_R = Q.store_thm("FILENAME_UNICITY_R[xlet_auto_match]",
`!f fv fv'. FILENAME f fv ==> (FILENAME f fv' <=> fv' = fv)`, filename_tac);

val FILENAME_UNICITY_L = Q.store_thm("FILENAME_UNICITY_L[xlet_auto_match]",
`!f f' fv. FILENAME f fv ==> (FILENAME f' fv <=> f' = f)`, filename_tac);

val FILENAME_STRING_UNICITY_R =
  Q.store_thm("FILENAME_STRING_UNICITY_R[xlet_auto_match]",
  `!f fv fv'. FILENAME f fv ==> (STRING_TYPE f fv' <=> fv' = fv)`,
  filename_tac);

val FILENAME_STRING_UNICITY_L =
  Q.store_thm("FILENAME_STRING_UNICITY_L[xlet_auto_match]",
  `!f f' fv. FILENAME f fv ==> (STRING_TYPE f' fv <=> f' = f)`, filename_tac);

val STRING_FILENAME_UNICITY_R =
  Q.store_thm("STRING_FILENAME_UNICITY_R[xlet_auto_match]",
  `!f fv fv'. STRING_TYPE f fv ==>
    (FILENAME f fv' <=> fv' = fv /\ ¬MEM #"\^@" (explode f) /\ strlen f < 256)`,
  filename_tac);

val STRING_FILENAME_UNICITY_L =
  Q.store_thm("STRING_FILENAME_UNICITY_L[xlet_auto_match]",
  `!f f' fv. STRING_TYPE f fv ==>
    (FILENAME f' fv <=> f' = f /\ ¬MEM #"\^@" (explode f) /\ strlen f < 256)`,
  filename_tac);

val BadFileName_UNICITY = Q.store_thm("BadFileName_UNICITY[xlet_auto_match]",
`!v1 v2. BadFileName_exn v1 ==> (BadFileName_exn v2 <=> v2 = v1)`,
  fs[BadFileName_exn_def]);

val InvalidFD_UNICITY = Q.store_thm("InvalidFD_UNICITY[xlet_auto_match]",
`!v1 v2. InvalidFD_exn v1 ==> (InvalidFD_exn v2 <=> v2 = v1)`,
  fs[InvalidFD_exn_def]);

val EndOfFile_UNICITY = Q.store_thm("EndOfFile_UNICITY[xlet_auto_match]",
`!v1 v2. EndOfFile_exn v1 ==> (EndOfFile_exn v2 <=> v2 = v1)`,
  fs[EndOfFile_exn_def]);

val UNIQUE_STDIO = Q.store_thm("UNIQUE_STDIO",
`!s. VALID_HEAP s ==> !fs1 fs2 H1 H2. (STDIO fs1 * H1) s /\
                                      (STDIO fs2 * H2) s ==>
              (fs1.infds = fs2.infds /\ fs1.files = fs2.files)`,
  rw[STDIO_def,STD_streams_def,SEP_CLAUSES,SEP_EXISTS_THM,STAR_COMM,STAR_ASSOC,cond_STAR] >>
  fs[Once STAR_COMM] >>
  imp_res_tac UNIQUE_IOFS >>
  cases_on`fs1` >> cases_on`fs2` >> fs[IO_fs_numchars_fupd]);

(* weak injection theorem *)
val STDIO_HPROP_INJ = Q.store_thm("STDIO_HPROP_INJ[hprop_inj]",
`HPROP_INJ (STDIO fs1) (STDIO fs2)
           (fs1.infds = fs2.infds /\ fs1.files = fs2.files)`,
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

val _ = export_theory();
