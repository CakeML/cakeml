open preamble basis
     charsetTheory lcsTheory diffTheory

val _ = new_theory "diffProg";

val _ = translation_extends"basisProg";

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

val _ = translate dynamic_lcs_def

(*val _ = translate (optimised_lcs_def |> REWRITE_RULE [GSYM mllistTheory.drop_def]);*)

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

val _ = translate(diff_alg2_def |> REWRITE_RULE [GSYM mllistTheory.drop_def]);

val longest_common_suffix_length_side = Q.prove(
  `!l l' n. longest_common_suffix_length_side l l' n = (LENGTH l = LENGTH l')`,
  ho_match_mp_tac (fetch "lcs" "longest_common_suffix_length_ind")
  >> rpt strip_tac
  >> rw[Once(fetch "-" "longest_common_suffix_length_side_def")]
  >> rw[EQ_IMP_THM]
  >> Cases_on `f = f'` >> fs[]
  >> fs[EQ_IMP_THM]
  >> fs[ADD1]) |> update_precondition

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

val diff_alg2_side_def = Q.prove(`
  !l r. diff_alg2_side l r  ⇔ T`,
  rw[fetch "-" "diff_alg2_side_def"]
  >> rw[longest_common_suffix_length_side]
  >> fs[mllistTheory.drop_def]
  >> metis_tac[diff_with_lcs_side_IMP,dynamic_lcs_correct]) |> update_precondition;

val notfound_string_def = Define`
  notfound_string f = concat[strlit"cake_diff: ";f;strlit": No such file or directory\n"]`;

val r = translate notfound_string_def;

val usage_string_def = Define`
  usage_string = strlit"Usage: diff <file> <file>\n"`;

val r = translate usage_string_def;

val _ = (append_prog o process_topdecs) `
  fun diff' fname1 fname2 =
    case TextIO.inputLinesFrom fname1 of
        NONE => TextIO.prerr_string (notfound_string fname1)
      | SOME lines1 =>
        case TextIO.inputLinesFrom fname2 of
            NONE => TextIO.prerr_string (notfound_string fname2)
          | SOME lines2 => TextIO.print_list (diff_alg2 lines1 lines2)`

val diff'_spec = Q.store_thm("diff'_spec",
  `FILENAME f1 fv1 ∧ FILENAME f2 fv2 /\
   hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"diff'"(get_ml_prog_state()))
     [fv1; fv2]
     (STDIO fs)
     (POSTv uv.
       &UNIT_TYPE () uv *
       STDIO (
         if inFS_fname fs (File f1) then
         if inFS_fname fs (File f2) then
           add_stdout fs (
              CONCAT (MAP explode
                          (diff_alg2 (all_lines fs (File f1))
                                     (all_lines fs (File f2)))))
         else add_stderr fs (explode (notfound_string f2))
         else add_stderr fs (explode (notfound_string f1))))`,
  xcf"diff'"(get_ml_prog_state())
  \\ xlet_auto_spec(SOME inputLinesFrom_spec)
  >- xsimpl
  \\ xmatch \\ reverse(Cases_on `inFS_fname fs (File f1)`)
  >- (fs[ml_translatorTheory.OPTION_TYPE_def]
      \\ reverse strip_tac
      >- (strip_tac >> EVAL_TAC)
      \\ xlet_auto >- xsimpl
      \\ xapp \\ xsimpl)
  \\ fs[ml_translatorTheory.OPTION_TYPE_def]
  \\ PURE_REWRITE_TAC [GSYM CONJ_ASSOC] \\ reverse strip_tac
  >- (EVAL_TAC \\ rw[])
  \\ xlet_auto_spec(SOME inputLinesFrom_spec)
  >- xsimpl
  \\ xmatch \\ reverse(Cases_on `inFS_fname fs (File f2)`)
  >- (fs[ml_translatorTheory.OPTION_TYPE_def]
      \\ reverse strip_tac
      >- (strip_tac >> EVAL_TAC)
      \\ xlet_auto >- xsimpl
      \\ xapp \\ xsimpl)
  \\ fs[ml_translatorTheory.OPTION_TYPE_def]
  \\ PURE_REWRITE_TAC [GSYM CONJ_ASSOC] \\ reverse strip_tac
  >- (EVAL_TAC \\ rw[])
  \\ xlet_auto >- xsimpl
  \\ xapp \\ rw[]);

val _ = (append_prog o process_topdecs) `
  fun diff u =
    case CommandLine.arguments () of
        (f1::f2::[]) => diff' f1 f2
      | _ => TextIO.prerr_string usage_string`;

val diff_spec = Q.store_thm("diff_spec",
  `hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"diff"(get_ml_prog_state()))
     [Conv NONE []]
     (STDIO fs * COMMANDLINE cl)
     (POSTv uv. &UNIT_TYPE () uv *
                STDIO (
                  if (LENGTH cl = 3) then
                  if inFS_fname fs (File (implode (EL 1 cl))) then
                  if inFS_fname fs (File (implode (EL 2 cl))) then
                  add_stdout fs (
                    CONCAT
                      (MAP explode (diff_alg2
                                      (all_lines fs (File (implode (EL 1 cl))))
                                      (all_lines fs (File (implode (EL 2 cl)))))))
                  else add_stderr fs (explode (notfound_string (implode (EL 2 cl))))
                  else add_stderr fs (explode (notfound_string (implode (EL 1 cl))))
                  else add_stderr fs (explode usage_string)) * (COMMANDLINE cl))`,
  strip_tac \\ xcf "diff" (get_ml_prog_state())
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)
  \\ xlet_auto >- xsimpl
  \\ Cases_on `cl` \\ fs[wfcl_def]
  \\ Cases_on `t` \\ fs[ml_translatorTheory.LIST_TYPE_def]
  >- (xmatch \\ xapp \\ xsimpl \\ CONV_TAC SWAP_EXISTS_CONV
      \\ qexists_tac `usage_string` \\ simp [theorem "usage_string_v_thm"]
      \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `fs` \\ xsimpl)
  \\ Cases_on `t'` \\ fs[ml_translatorTheory.LIST_TYPE_def]
  >- (xmatch \\ xapp \\ xsimpl \\ CONV_TAC SWAP_EXISTS_CONV
      \\ qexists_tac `usage_string` \\ simp [theorem "usage_string_v_thm"]
      \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `fs` \\ xsimpl)
  \\ xmatch
  \\ reverse(Cases_on `t`) \\ fs[ml_translatorTheory.LIST_TYPE_def]
  \\ PURE_REWRITE_TAC [GSYM CONJ_ASSOC] \\ (reverse strip_tac >- (EVAL_TAC \\ rw[]))
  >- (xapp \\ xsimpl \\ CONV_TAC SWAP_EXISTS_CONV
      \\ qexists_tac `usage_string` \\ simp [theorem "usage_string_v_thm"]
      \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `fs` \\ xsimpl)
  \\ xapp \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `fs`
  \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `implode h''`
  \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `implode h'`
  \\ xsimpl \\ fs[FILENAME_def,mlstringTheory.explode_implode]
  \\ fs[mlstringTheory.implode_def,mlstringTheory.strlen_def]
  \\ fs[validArg_def,EVERY_MEM]
  \\ rw[] \\ xsimpl);

val st = get_ml_prog_state();

val name = "diff"
val spec = diff_spec |> UNDISCH
  |> SIMP_RULE (srw_ss())[STDIO_def] |> add_basis_proj
val (sem_thm,prog_tm) = call_thm st name spec

val diff_prog_def = Define`diff_prog = ^prog_tm`;

val diff_semantics = save_thm("diff_semantics",
  sem_thm
  |> REWRITE_RULE[GSYM diff_prog_def]
  |> DISCH_ALL
  |> CONV_RULE(LAND_CONV EVAL)
  |> REWRITE_RULE[AND_IMP_INTRO,GSYM CONJ_ASSOC]
  |> SIMP_RULE(srw_ss())[STD_streams_add_stdout,STD_streams_add_stderr,Q.ISPEC`STD_streams`COND_RAND]);

val _ = export_theory ();
