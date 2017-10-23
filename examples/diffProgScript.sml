open preamble ml_translatorLib ml_progLib
     cfTacticsLib basisFunctionsLib
     rofsFFITheory mlfileioProgTheory ioProgTheory
     charsetTheory lcsTheory diffTheory

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

val _ = translate (optimised_lcs_def |> REWRITE_RULE [GSYM mllistTheory.drop_def]);

val dynamic_lcs_row_side_def = Q.prove(
`∀h l previous_col previous_row diagonal.
   dynamic_lcs_row_side h l previous_col previous_row diagonal ⇔
   (LENGTH l <= LENGTH previous_row)`,
  Induct_on `l`
  >> rw[Once(fetch "-" "dynamic_lcs_row_side_def")]
  >> Cases_on `diagonal`
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
  fun diff'' fd1 fd2 n =
    case FileIO.inputLine fd1 of
        NONE => List.app print (diff_alg [] (FileIO.inputLines fd2))
      | SOME line1 =>
        case FileIO.inputLine fd2 of
        NONE => List.app print (diff_alg (line1::FileIO.inputLines fd1) [])
      | SOME line2 =>
        if line1 = line2 then
          diff'' fd1 fd2 (n+1)
        else
          List.app print (diff_alg (line1::FileIO.inputLines fd1) (line2::FileIO.inputLines fd2))`

val _ = (append_prog o process_topdecs) `
  fun diff' fname1 fname2 =
    case FileIO.inputLinesFrom fname1 of
        NONE => print_err (notfound_string fname1)
      | SOME lines1 =>
        case FileIO.inputLinesFrom fname2 of
            NONE => print_err (notfound_string fname2)
          | SOME lines2 => List.app print (diff_alg lines1 lines2)`

val take_add_one_lemma = Q.prove(
  `!n l. n < LENGTH l ==> TAKE (n+1) l = TAKE n l ++ [EL n l]`,
  Induct >> Cases >> fs[TAKE] >> fs[ADD1]);

val diff'_spec = Q.store_thm("diff'_spec",
  `FILENAME f1 fv1 ∧ FILENAME f2 fv2 /\
   hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"diff'"(get_ml_prog_state()))
     [fv1; fv2]
     (ROFS fs * STDOUT out * STDERR err)
     (POSTv uv. &UNIT_TYPE () uv
                * ROFS fs *
                STDOUT (out ++
                  if inFS_fname fs f1 /\ inFS_fname fs f2 then
                    CONCAT (MAP explode
                                (diff_alg (all_lines fs f1)
                                          (all_lines fs f2)))
                  else "") *
                STDERR (err ++
                  if inFS_fname fs f1 /\ inFS_fname fs f2 then ""
                  else if inFS_fname fs f1 then explode (notfound_string f2)
                  else explode (notfound_string f1)))`,
  xcf"diff'"(get_ml_prog_state())
  \\ xlet `POSTv sv. &OPTION_TYPE (LIST_TYPE STRING_TYPE)
            (if inFS_fname fs f1 then
               SOME(all_lines fs f1)
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
               SOME(all_lines fs f2)
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
                                      (all_lines fs f1)
                                      (all_lines fs f2)) sv
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
`CARD (set (MAP FST fs.infds)) < 255
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"diff"(get_ml_prog_state()))
     [Conv NONE []]
     (ROFS fs * STDOUT out * STDERR err * COMMANDLINE cl)
     (POSTv uv. &UNIT_TYPE () uv
                *
                STDOUT (out ++
                  if (LENGTH cl = 3) /\ inFS_fname fs (implode (EL 1 cl)) /\ inFS_fname fs (implode (EL 2 cl)) then
                    CONCAT
                      (MAP explode (diff_alg
                                      (all_lines fs (implode (EL 1 cl)))
                                      (all_lines fs (implode (EL 2 cl)))))
                  else "") *
                STDERR (err ++
                  if (LENGTH cl = 3) /\ inFS_fname fs (implode (EL 1 cl)) /\ inFS_fname fs (implode (EL 2 cl)) then ""
                  else if LENGTH cl <> 3 then explode (usage_string)
                  else if inFS_fname fs (implode (EL 1 cl)) then explode (notfound_string (implode (EL 2 cl)))
                  else explode (notfound_string (implode (EL 1 cl)))) * (COMMANDLINE cl * ROFS fs))`,
  strip_tac \\ xcf "diff" (get_ml_prog_state())
  \\ xlet `POSTv v. &UNIT_TYPE () v * ROFS fs * STDOUT out * STDERR err * COMMANDLINE cl`
  >- (xcon \\ xsimpl)
  \\ reverse(Cases_on`wfcl cl`) >- (fs[mlcommandLineProgTheory.COMMANDLINE_def] \\ xpull)
  \\ xlet`POSTv v. &LIST_TYPE STRING_TYPE (TL (MAP implode cl)) v * ROFS fs * STDOUT out * STDERR err * COMMANDLINE cl`
  >- (xapp \\ xsimpl \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`cl` \\ xsimpl)
  \\ Cases_on `cl` \\ fs[mlcommandLineProgTheory.wfcl_def]
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
  \\ fs[commandLineFFITheory.validArg_def,EVERY_MEM]);

val st = get_ml_prog_state();

val name = "diff"
val spec = diff_spec |> UNDISCH |> ioProgLib.add_basis_proj
val (sem_thm,prog_tm) = ioProgLib.call_thm st name spec

val diff_prog_def = Define`diff_prog = ^prog_tm`;

val diff_semantics = save_thm("diff_semantics",
  sem_thm
  |> REWRITE_RULE[GSYM diff_prog_def]
  |> DISCH_ALL
  |> REWRITE_RULE[AND_IMP_INTRO]
  |> CONV_RULE(LAND_CONV EVAL)
  |> SIMP_RULE(srw_ss())[]);

val _ = export_theory ();
