(*
   Functions for reading every line from a file. TODO: move to basis?
*)
open preamble ml_translatorLib ml_progLib
     cfTacticsLib basisFunctionsLib
     rofsFFITheory mlfileioProgTheory ioProgTheory
     charsetTheory;

val _ = new_theory "inputLinesProg";

val _ = translation_extends"ioProg";

val _ = (append_prog o process_topdecs) `
  fun inputLines fd =
    case FileIO.inputLine fd of
        NONE => []
      | SOME l => l::inputLines fd`

val inputLines_spec = Q.store_thm("input_lines_spec",
  `∀fnm fnv fs.
   WORD (fd:word8) fdv ∧ validFD (w2n fd) fs ⇒
   app (p:'ffi ffi_proj)
     ^(fetch_v "inputLines"(get_ml_prog_state())) [fdv]
     (ROFS fs)
     (POSTv fcv.
       &LIST_TYPE STRING_TYPE (MAP (\x. strcat (implode x) (implode "\n")) (linesFD (w2n fd) fs)) fcv *
       ROFS (bumpAllFD (w2n fd) fs))`,
  Induct_on`linesFD (w2n fd) fs` \\ rw[]
  >- (qpat_x_assum`[] = _`(assume_tac o SYM) \\ fs[]
      \\ xcf"inputLines"(get_ml_prog_state())
      \\ xlet`POSTv x. &OPTION_TYPE STRING_TYPE (OPTION_MAP implode (FDline (w2n fd) fs))  x *
                     ROFS (bumpLineFD (w2n fd) fs)`
      >- (xapp \\ fs[])
      \\ rfs[GSYM FDline_NONE_linesFD,ml_translatorTheory.OPTION_TYPE_def]
      \\ xmatch
      \\ xcon
      \\ imp_res_tac FDline_NONE_bumpAll_bumpLine
      \\ xsimpl \\ fs[ml_translatorTheory.LIST_TYPE_def])
  \\ qpat_x_assum`_::_ = _`(assume_tac o SYM) \\ fs[]
  \\ xcf"inputLines"(get_ml_prog_state())
  \\ xlet`POSTv x. &OPTION_TYPE STRING_TYPE (OPTION_MAP implode (FDline (w2n fd) fs))  x *
                   ROFS (bumpLineFD (w2n fd) fs)`
  >- ( xapp \\ fs[] )
  \\ Cases_on`FDline (w2n fd) fs` \\ fs[FDline_NONE_linesFD]
  \\ fs[ml_translatorTheory.OPTION_TYPE_def]
  \\ xmatch
  \\ drule linesFD_eq_cons_imp \\ strip_tac \\ fs[] \\ rveq
  \\ rename1`FDline _ _ = SOME ln`
  \\ rveq
  \\ xlet `POSTv fcv.
     &LIST_TYPE STRING_TYPE
        (MAP (λx. implode x ^ implode "\n") (linesFD (w2n fd) (bumpLineFD (w2n fd) fs)))
        fcv * ROFS (bumpAllFD (w2n fd) (bumpLineFD (w2n fd) fs))`  
  >- (xapp \\ qexists_tac `emp` \\ qexists_tac `bumpLineFD (w2n fd) fs` \\
      qexists_tac `fd` \\ fs[SEP_CLAUSES,SEP_IMP_REFL] \\ xsimpl)
  \\ xcon \\ xsimpl \\ fs[ml_translatorTheory.LIST_TYPE_def]
  \\ fs[mlstringTheory.implode_def,ml_translatorTheory.STRING_TYPE_def,mlstringTheory.strcat_def]
  \\ drule linesFD_eq_cons_imp \\ fs[]);

val _ = (append_prog o process_topdecs) `
  fun inputLinesFrom fname =
    let
      val fd = FileIO.openIn fname
      val lines = inputLines fd
    in
      FileIO.close fd; SOME lines
    end handle FileIO.BadFileName => NONE`

val all_lines_def = Define
  `all_lines fs fname = MAP (\x. strcat (implode x) (implode "\n"))
                            (splitlines (THE (ALOOKUP fs.files fname)))`

val inputLinesFrom_spec = Q.store_thm("inputLinesFrom_spec",
  `FILENAME f fv /\
   CARD (FDOM (alist_to_fmap fs.infds)) < 255
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"inputLinesFrom"(get_ml_prog_state()))
     [fv]
     (ROFS fs)
     (POSTv sv. &OPTION_TYPE (LIST_TYPE STRING_TYPE)
            (if inFS_fname fs f then
               SOME(all_lines fs f)
             else NONE) sv
             * ROFS fs)`,
  PURE_REWRITE_TAC [all_lines_def]
  \\ xcf"inputLinesFrom"(get_ml_prog_state())
  \\ reverse(xhandle`POST
       (λv. &OPTION_TYPE (LIST_TYPE STRING_TYPE)
         (if inFS_fname fs f then SOME(MAP (\x. strcat (implode x) (implode "\n")) (splitlines (THE (ALOOKUP fs.files f)))) else NONE) v * ROFS fs)
       (λe. &(BadFileName_exn e ∧ ¬inFS_fname fs f) * ROFS fs)`)
  >- (xcases \\ fs[BadFileName_exn_def]
      \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
      \\ xcon \\ xsimpl \\ fs[ml_translatorTheory.OPTION_TYPE_def])
  >- xsimpl  
  \\ xlet`POST (λv. &(WORD ((n2w (nextFD fs)):word8) v ∧ validFD (nextFD fs) (openFileFS f fs) ∧
                      inFS_fname fs f) * ROFS (openFileFS f fs))
               (λe. &(BadFileName_exn e ∧ ¬inFS_fname fs f) * ROFS fs)`
  >- (xapp \\ fs[])
  >- xsimpl
  \\ xlet`POSTv v. &LIST_TYPE STRING_TYPE (MAP (\x. strcat (implode x) (implode "\n")) (splitlines (THE (ALOOKUP fs.files f)))) v * ROFS (bumpAllFD (nextFD fs) (openFileFS f fs))`
  >- (xapp \\ instantiate \\ qexists_tac `emp` \\ qexists_tac `openFileFS f fs`
      \\ fs[FDOM_alist_to_fmap] \\ drule (GEN_ALL nextFD_ltX) \\ strip_tac
      \\ fs[] \\ xsimpl
      \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS \\ fs[]
      \\ imp_res_tac ALOOKUP_inFS_fname_openFileFS_nextFD \\ simp[linesFD_def]
      \\ Cases_on`0 < LENGTH content` \\ fs[libTheory.the_def,LENGTH_NIL])
  \\ xlet`POSTv v. &UNIT_TYPE () v * ROFS fs`
  >- (fs[FDOM_alist_to_fmap] \\ imp_res_tac nextFD_ltX
      \\ xapp \\ qexists_tac `emp` \\ qexists_tac `bumpAllFD (nextFD fs) (openFileFS f fs)`
      \\ instantiate \\ xsimpl
      \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS
      \\ imp_res_tac ALOOKUP_inFS_fname_openFileFS_nextFD \\ simp[linesFD_def]
      \\ fs[bumpAllFD_def,libTheory.the_def]
      \\ fs[openFileFS_def,openFile_def,A_DELKEY_def]
      \\ rpt (pop_assum kall_tac)
      \\ `FILTER (λp. FST p ≠ nextFD fs) fs.infds = fs.infds`
          suffices_by(fs[] \\ Cases_on `fs` \\ fs[RO_fs_fn_updates] \\ xsimpl)
      \\ assume_tac nextFD_NOT_MEM
      \\ fs[FILTER_EQ_ID,EVERY_MEM] \\ rpt strip_tac
      \\ Cases_on `p` \\ Cases_on `r` \\ fs[] \\ rfs[])
  \\ xcon \\ xsimpl \\ fs[ml_translatorTheory.OPTION_TYPE_def]);

val _ = export_theory ();
