(*
  diff example: find a patch representing the difference between two files.
*)
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

val diff_alg2_side_def = Q.prove(`
  !l r. diff_alg2_side l r  ⇔ T`,
  rw[fetch "-" "diff_alg2_side_def"]
  >> rw[longest_common_suffix_length_side]
  >> fs[mllistTheory.drop_def]) |> update_precondition;

val notfound_string_def = Define`
  notfound_string f = concat[strlit"cake_diff: ";f;strlit": No such file or directory\n"]`;

val r = translate notfound_string_def;

val usage_string_def = Define`
  usage_string = strlit"Usage: diff <file> <file>\n"`;

val r = translate usage_string_def;

val _ = (append_prog o process_topdecs) `
  fun diff' fname1 fname2 =
    case TextIO.inputLinesFrom fname1 of
        None => TextIO.output TextIO.stdErr (notfound_string fname1)
      | Some lines1 =>
        case TextIO.inputLinesFrom fname2 of
            None => TextIO.output TextIO.stdErr (notfound_string fname2)
          | Some lines2 => TextIO.print_list (diff_alg2 lines1 lines2)`

Theorem diff'_spec:
   FILENAME f1 fv1 ∧ FILENAME f2 fv2 /\
   hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"diff'"(get_ml_prog_state()))
     [fv1; fv2]
     (STDIO fs)
     (POSTv uv.
       &UNIT_TYPE () uv *
       STDIO (
         if inFS_fname fs f1 then
         if inFS_fname fs f2 then
           add_stdout fs (
              concat ((diff_alg2 (all_lines fs f1)
                                 (all_lines fs f2))))
         else add_stderr fs (notfound_string f2)
         else add_stderr fs (notfound_string f1)))
Proof
  xcf"diff'"(get_ml_prog_state())
  \\ xlet_auto_spec(SOME inputLinesFrom_spec)
  >- xsimpl
  \\ xmatch \\ reverse(Cases_on `inFS_fname fs f1`)
  >- (fs[OPTION_TYPE_def]
      \\ reverse strip_tac
      >- (strip_tac >> EVAL_TAC)
      \\ xlet_auto >- xsimpl
      \\ xapp_spec output_stderr_spec \\ xsimpl)
  \\ fs[OPTION_TYPE_def]
  \\ PURE_REWRITE_TAC [GSYM CONJ_ASSOC] \\ reverse strip_tac
  >- (EVAL_TAC \\ rw[])
  \\ xlet_auto_spec(SOME inputLinesFrom_spec)
  >- xsimpl
  \\ xmatch \\ reverse(Cases_on `inFS_fname fs f2`)
  >- (fs[OPTION_TYPE_def]
      \\ reverse strip_tac
      >- (strip_tac >> EVAL_TAC)
      \\ xlet_auto >- xsimpl
      \\ xapp_spec output_stderr_spec \\ xsimpl)
  \\ fs[OPTION_TYPE_def]
  \\ PURE_REWRITE_TAC [GSYM CONJ_ASSOC] \\ reverse strip_tac
  >- (EVAL_TAC \\ rw[])
  \\ xlet_auto >- xsimpl
  \\ xapp \\ rw[]
QED

val _ = (append_prog o process_topdecs) `
  fun diff u =
    case CommandLine.arguments () of
        (f1::f2::[]) => diff' f1 f2
      | _ => TextIO.output TextIO.stdErr usage_string`;

val diff_sem_def = Define`
  diff_sem cl fs =
    if (LENGTH cl = 3) then
    if inFS_fname fs (EL 1 cl) then
    if inFS_fname fs (EL 2 cl) then
    add_stdout fs (
      concat
        (diff_alg2
           (all_lines fs (EL 1 cl))
           (all_lines fs (EL 2 cl))))
    else add_stderr fs (notfound_string (EL 2 cl))
    else add_stderr fs (notfound_string (EL 1 cl))
    else add_stderr fs usage_string`;

Theorem diff_spec:
   hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"diff"(get_ml_prog_state()))
     [Conv NONE []]
     (STDIO fs * COMMANDLINE cl)
     (POSTv uv. &UNIT_TYPE () uv *
                STDIO (diff_sem cl fs) * (COMMANDLINE cl))
Proof
  once_rewrite_tac[diff_sem_def]
  \\ strip_tac \\ xcf "diff" (get_ml_prog_state())
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)
  \\ xlet_auto >- xsimpl
  \\ Cases_on `cl` \\ fs[wfcl_def]
  \\ Cases_on `t` \\ fs[ml_translatorTheory.LIST_TYPE_def]
  >- (xmatch \\ xapp_spec output_stderr_spec \\ xsimpl \\ CONV_TAC SWAP_EXISTS_CONV
      \\ qexists_tac `usage_string` \\ simp [theorem "usage_string_v_thm"]
      \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `fs` \\ xsimpl)
  \\ Cases_on `t'` \\ fs[ml_translatorTheory.LIST_TYPE_def]
  >- (xmatch \\ xapp_spec output_stderr_spec \\ xsimpl \\ CONV_TAC SWAP_EXISTS_CONV
      \\ qexists_tac `usage_string` \\ simp [theorem "usage_string_v_thm"]
      \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `fs` \\ xsimpl)
  \\ xmatch
  \\ reverse(Cases_on `t`) \\ fs[ml_translatorTheory.LIST_TYPE_def]
  \\ PURE_REWRITE_TAC [GSYM CONJ_ASSOC] \\ (reverse strip_tac >- (EVAL_TAC \\ rw[]))
  >- (xapp_spec output_stderr_spec \\ xsimpl \\ CONV_TAC SWAP_EXISTS_CONV
      \\ qexists_tac `usage_string` \\ simp [theorem "usage_string_v_thm"]
      \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `fs` \\ xsimpl)
  \\ xapp \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `fs`
  \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `h''`
  \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `h'`
  \\ xsimpl \\ fs[FILENAME_def]
  \\ fs[validArg_def,EVERY_MEM]
QED

val st = get_ml_prog_state();

Theorem diff_whole_prog_spec:
   hasFreeFD fs ⇒
   whole_prog_spec ^(fetch_v"diff"st) cl fs NONE ((=) (diff_sem cl fs))
Proof
  rw[whole_prog_spec_def]
  \\ qexists_tac`diff_sem cl fs`
  \\ reverse conj_tac
  >- ( rw[diff_sem_def,GSYM add_stdo_with_numchars,with_same_numchars] )
  \\ simp [SEP_CLAUSES]
  \\ match_mp_tac (MP_CANON (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH diff_spec))))
  \\ xsimpl
QED

val name = "diff"
val (sem_thm,prog_tm) = whole_prog_thm st name (UNDISCH diff_whole_prog_spec)
val diff_prog_def = Define`diff_prog = ^prog_tm`;

val diff_semantics = save_thm("diff_semantics",
  sem_thm |> REWRITE_RULE[GSYM diff_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[GSYM CONJ_ASSOC,AND_IMP_INTRO]);

val _ = export_theory ();
