open preamble ml_translatorLib ml_progLib
     cfTacticsLib basisFunctionsLib
     rofsFFITheory mlfileioProgTheory ioProgTheory
     charsetTheory lcsTheory diffTheory;

val _ = new_theory "diffProg";

val _ = translation_extends"ioProg";

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_thm") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  in def end

val _ = find_def_for_const := def_of_const;

val _ = translate (optimised_lcs_def);

val dynamic_lcs_row_side_def = Q.prove(
`∀h l previous_col previous_row diagonal.
   dynamic_lcs_row_side h l previous_col previous_row diagonal ⇔
   (LENGTH l <= LENGTH previous_row)`,
  Induct_on `l`
  >> rw[Once(fetch "-" "dynamic_lcs_row_side_def")]
  >> Cases_on `previous_row`
  >> fs[] >> metis_tac[]) |> update_precondition;

val dynamic_lcs_rows_side_def = Q.prove(
  `∀l r previous_row.
   dynamic_lcs_rows_side l r previous_row ⇔
   (l = [] \/ LENGTH r <= LENGTH previous_row)`,
  Induct_on `l`
  >> rw[Once(fetch "-" "dynamic_lcs_rows_side_def"),dynamic_lcs_row_side_def,dynamic_lcs_length])
  |> update_precondition;

val dynamic_lcs_side_def = Q.prove(
  `∀l r. dynamic_lcs_side l r ⇔ T`,
  rw[fetch "-" "dynamic_lcs_side_def",dynamic_lcs_rows_side_def,LENGTH_REPLICATE])
  |> update_precondition;

val optimised_lcs_side_def = Q.prove(
  `∀l r. optimised_lcs_side l r ⇔ T`,
  rw[fetch "-" "optimised_lcs_side_def",dynamic_lcs_side_def]) |> update_precondition;

val _ = translate diff_alg_def;

val diff_with_lcs_side_IMP = Q.prove(
  `!l l' n l'' n'.
   lcs l l' l'' ==> diff_with_lcs_side l l' n l'' n'`,
  Induct_on `l`
  >- fs[Once(fetch "-" "diff_with_lcs_side_def")]
  >> PURE_ONCE_REWRITE_TAC [fetch "-" "diff_with_lcs_side_def"]
  >> rpt strip_tac
  >> drule lcs_split
  >> drule lcs_split2  
  >> drule split_lcs_optimal_substructure
  >> rpt strip_tac  
  >> fs[]
  >> rpt(CHANGED_TAC(TRY(qpat_x_assum `a::b = x` (assume_tac o GSYM))))
  >> rfs[]
  >> metis_tac[list_distinct]);

val diff_alg_side_def = Q.prove(`
  !l r. diff_alg_side l r  ⇔ T`,
  rw[fetch "-" "diff_alg_side_def"]
  >> metis_tac[diff_with_lcs_side_IMP,optimised_lcs_correct]) |> update_precondition;

val notfound_string_def = Define`
  notfound_string f = concat[strlit"cake_diff: ";f;strlit": No such file or directory\n"]`;

val r = translate notfound_string_def;

val usage_string_def = Define`
  usage_string = strlit"Usage: diff <file> <file>\n"`;

val r = translate usage_string_def;    

val _ = (append_prog o process_topdecs) `
  fun inputLines fd =
    case FileIO.inputLine fd of
        NONE => []
      | SOME l => l::inputLines fd`

val input_lines_spec = Q.store_thm("input_lines_spec",
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

val inputLinesFrom_spec = Q.store_thm("inputLinesFrom_spec",
  `FILENAME f fv /\
   CARD (FDOM (alist_to_fmap fs.infds)) < 255
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"inputLinesFrom"(get_ml_prog_state()))
     [fv]
     (ROFS fs)
     (POSTv sv. &OPTION_TYPE (LIST_TYPE STRING_TYPE)
            (if inFS_fname fs f then
               SOME(MAP (\x. strcat (implode x) (implode "\n"))
                        (splitlines (THE (ALOOKUP fs.files f))))
             else NONE) sv
                * ROFS fs)`,
  xcf"inputLinesFrom"(get_ml_prog_state())
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
  
val _ = (append_prog o process_topdecs) `
  fun diff' fname1 fname2 =
    case inputLinesFrom fname1 of
        NONE => print_err (notfound_string fname1)
      | SOME lines1 =>
        case inputLinesFrom fname2 of
            NONE => print_err (notfound_string fname2)
          | SOME lines2 => List.app print (diff_alg lines1 lines2)`

val take_add_one_lemma = Q.prove(
  `!n l. n < LENGTH l ==> TAKE (n+1) l = TAKE n l ++ [EL n l]`,
  Induct >> Cases >> fs[TAKE] >> fs[ADD1]);

val diff'_spec = Q.store_thm("diff'_spec",
  `FILENAME f1 fv1 ∧ FILENAME f2 fv2 /\
   CARD (FDOM (alist_to_fmap fs.infds)) < 255
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"diff'"(get_ml_prog_state()))
     [fv1; fv2]
     (ROFS fs * STDOUT out * STDERR err)
     (POSTv uv. &UNIT_TYPE () uv
                * ROFS fs *
                STDOUT (out ++
                  if inFS_fname fs f1 /\ inFS_fname fs f2 then
                    CONCAT
                      (MAP explode (diff_alg
                                      (MAP (\x. strcat (implode x) (implode "\n")) (splitlines (THE (ALOOKUP fs.files f1))))
                                      (MAP (\x. strcat (implode x) (implode "\n")) (splitlines (THE (ALOOKUP fs.files f2))))))
                  else "") *
                STDERR (err ++
                  if inFS_fname fs f1 /\ inFS_fname fs f2 then ""
                  else if inFS_fname fs f1 then explode (notfound_string f2)
                  else explode (notfound_string f1)))`,
  xcf"diff'"(get_ml_prog_state())
  \\ xlet `POSTv sv. &OPTION_TYPE (LIST_TYPE STRING_TYPE)
            (if inFS_fname fs f1 then
               SOME(MAP (\x. strcat (implode x) (implode "\n"))
                        (splitlines (THE (ALOOKUP fs.files f1))))
             else NONE) sv * ROFS fs * STDOUT out * STDERR err`
  >- (xapp \\ instantiate \\ xsimpl)
  \\ xmatch \\ reverse(Cases_on `inFS_fname fs f1`)
  >- (fs[ml_translatorTheory.OPTION_TYPE_def]
      \\ reverse strip_tac
      >- (strip_tac >> EVAL_TAC)
      \\ xlet`POSTv v. &STRING_TYPE (notfound_string f1) v
                       * ROFS fs * STDOUT out * STDERR err`
      >- (xapp \\ xsimpl \\ qexists_tac `f1` \\ fs[FILENAME_def])
      \\ xapp \\ instantiate \\ xsimpl
      \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `err`
      \\ xsimpl)
  \\ fs[ml_translatorTheory.OPTION_TYPE_def]
  \\ PURE_REWRITE_TAC [GSYM CONJ_ASSOC] \\ reverse strip_tac
  >- (EVAL_TAC \\ rw[])
  \\ xlet `POSTv sv. &OPTION_TYPE (LIST_TYPE STRING_TYPE)
            (if inFS_fname fs f2 then
               SOME(MAP (\x. strcat (implode x) (implode "\n"))
                        (splitlines (THE (ALOOKUP fs.files f2))))
             else NONE) sv * ROFS fs * STDOUT out * STDERR err`
  >- (xapp \\ instantiate \\ xsimpl)
  \\ xmatch \\ reverse(Cases_on `inFS_fname fs f2`)
  >- (fs[ml_translatorTheory.OPTION_TYPE_def]
      \\ reverse strip_tac
      >- (strip_tac >> EVAL_TAC)
      \\ xlet`POSTv v. &STRING_TYPE (notfound_string f2) v
                       * ROFS fs * STDOUT out * STDERR err`
      >- (xapp \\ xsimpl \\ qexists_tac `f2` \\ fs[FILENAME_def])
      \\ xapp \\ instantiate \\ xsimpl
      \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `err`
      \\ xsimpl)
  \\ fs[ml_translatorTheory.OPTION_TYPE_def]
  \\ PURE_REWRITE_TAC [GSYM CONJ_ASSOC] \\ reverse strip_tac
  >- (EVAL_TAC \\ rw[])
  \\ xlet `POSTv sv. &LIST_TYPE STRING_TYPE (diff_alg
                                      (MAP (\x. strcat (implode x) (implode "\n")) (splitlines (THE (ALOOKUP fs.files f1))))
                                      (MAP (\x. strcat (implode x) (implode "\n")) (splitlines (THE (ALOOKUP fs.files f2))))) sv
                * ROFS fs * STDOUT out * STDERR err`
  >- (xapp \\ instantiate \\ xsimpl)
  \\ qpat_abbrev_tac `a1 = diff_alg _ _`
  \\ xapp_spec (INST_TYPE [alpha |-> ``:mlstring``] mllistProgTheory.app_spec)
  \\ qexists_tac `emp` \\ qexists_tac `a1`
  \\ qexists_tac `\n. ROFS fs * STDOUT(out ++ CONCAT(TAKE n (MAP explode a1))) * STDERR err`
  \\ xsimpl \\ fs[GSYM MAP_TAKE] \\ xsimpl \\ instantiate \\ rpt strip_tac
  \\ xapp \\ instantiate \\ xsimpl \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac `STRCAT out (CONCAT (MAP explode (TAKE n a1)))` \\ xsimpl
  \\ imp_res_tac take_add_one_lemma \\ fs[] \\ xsimpl);

val _ = (append_prog o process_topdecs) `
  fun diff u =
    case Commandline.arguments () of
        (f1::f2::[]) => diff' f1 f2
      | _ => print_err usage_string`

val diff_spec = Q.store_thm("diff_spec",
`(*FILENAME f1 fv1 ∧ FILENAME f2 fv2 /\ *)
   cl <> [] /\ EVERY validArg cl
   /\ LENGTH (FLAT cl) + LENGTH cl ≤ 256
   /\ CARD (set (MAP FST fs.infds)) < 255
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"diff"(get_ml_prog_state()))
     [Conv NONE []]
     (ROFS fs * STDOUT out * STDERR err * COMMANDLINE cl)
     (POSTv uv. &UNIT_TYPE () uv
                * ROFS fs *
                STDOUT (out ++
                  if (LENGTH cl = 3) /\ inFS_fname fs (implode (EL 1 cl)) /\ inFS_fname fs (implode (EL 2 cl)) then
                    CONCAT
                      (MAP explode (diff_alg
                                      (MAP (\x. strcat (implode x) (implode "\n")) (splitlines (THE (ALOOKUP fs.files (implode (EL 1 cl))))))
                                      (MAP (\x. strcat (implode x) (implode "\n")) (splitlines (THE (ALOOKUP fs.files (implode (EL 2 cl))))))))
                  else "") *
                STDERR (err ++
                  if (LENGTH cl = 3) /\ inFS_fname fs (implode (EL 1 cl)) /\ inFS_fname fs (implode (EL 2 cl)) then ""
                  else if LENGTH cl <> 3 then explode (usage_string)
                  else if inFS_fname fs (implode (EL 1 cl)) then explode (notfound_string (implode (EL 2 cl)))
                  else explode (notfound_string (implode (EL 1 cl)))) * COMMANDLINE cl)`,
  strip_tac \\ xcf "diff" (get_ml_prog_state())
  \\ xlet `POSTv v. &UNIT_TYPE () v * ROFS fs * STDOUT out * STDERR err * COMMANDLINE cl`
  >- (xcon \\ xsimpl)
  \\ xlet`POSTv v. &LIST_TYPE STRING_TYPE (TL (MAP implode cl)) v * ROFS fs * STDOUT out * STDERR err * COMMANDLINE cl`
  >- (xapp \\ instantiate \\ xsimpl
      \\ simp[MAP_TL,NULL_EQ,LENGTH_FLAT,MAP_MAP_o,o_DEF] (* TODO: this is duplicated in catProg and bootstrap and grepProg and now also here *)
      \\ Q.ISPECL_THEN[`STRLEN`]mp_tac SUM_MAP_PLUS
      \\ disch_then(qspecl_then[`K 1`,`cl`]mp_tac)
      \\ simp[MAP_K_REPLICATE,SUM_REPLICATE,GSYM LENGTH_FLAT])
  \\ Cases_on `cl` \\ fs[]
  \\ Cases_on `t` \\ fs[ml_translatorTheory.LIST_TYPE_def]
  >- (xmatch \\ xapp \\ xsimpl \\ CONV_TAC SWAP_EXISTS_CONV
      \\ qexists_tac `usage_string` \\ simp [theorem "usage_string_v_thm"]
      \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `err` \\ xsimpl)
  \\ Cases_on `t'` \\ fs[ml_translatorTheory.LIST_TYPE_def]
  >- (xmatch \\ xapp \\ xsimpl \\ CONV_TAC SWAP_EXISTS_CONV
      \\ qexists_tac `usage_string` \\ simp [theorem "usage_string_v_thm"]
      \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `err` \\ xsimpl)
  \\ xmatch
  \\ reverse(Cases_on `t`) \\ fs[ml_translatorTheory.LIST_TYPE_def]
  \\ PURE_REWRITE_TAC [GSYM CONJ_ASSOC] \\ (reverse strip_tac >- (EVAL_TAC \\ rw[]))
  >- (xapp \\ xsimpl \\ CONV_TAC SWAP_EXISTS_CONV
      \\ qexists_tac `usage_string` \\ simp [theorem "usage_string_v_thm"]
      \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `err` \\ xsimpl)
  \\ xapp \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `out`
  \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `fs`
  \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `implode h''`
  \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `implode h'`
  \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `err`
  \\ xsimpl \\ fs[FILENAME_def,mlstringTheory.explode_implode]
  \\ fs[mlstringTheory.implode_def,mlstringTheory.strlen_def]
  \\ fs[commandLineFFITheory.validArg_def,EVERY_MEM]
  \\ qpat_abbrev_tac `a1 = STDOUT _` \\ xsimpl);

val _ = export_theory ();
