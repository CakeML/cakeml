(*
  The CakeML program implementing the word frequency application.
  This is produced by a combination of translation and CF verification.
*)

open preamble
     ml_translatorLib cfTacticsLib basisFunctionsLib cfLetAutoLib
     ioProgLib basisProgTheory
     balanced_mapTheory wordfreqTheory

(*
  IMPORTANT: The first thing you should do is rename this file to
    wordfreqProgScript.sml
*)

val _ = new_theory "wordfreqProg";

val _ = translation_extends"basisProg";

(* avoid printing potentially very long output *)
val _ = Globals.max_print_depth := 20

(* Translation of balanced binary tree functions *)

val res = translate lookup_def;
val res = translate singleton_def;
val res = translate ratio_def;
val res = translate size_def;
val res = translate delta_def;
val _ = next_ml_names := ["balanceL","balanceR"];
val res = translate balanceL_def;
val res = translate balanceR_def;
val res = translate insert_def;
val res = translate empty_def;
val _ = next_ml_names := ["foldrWithKey","toAscList"];
val res = translate foldrWithKey_def;
val res = translate toAscList_def;

(* Translation of wordfreq helper functions *)

val res = translate lookup0_def;
val res = translate insert_word_def;
val res = translate insert_line_def;

val format_output_def = Define`
  format_output (k,v) = concat [k; strlit": "; toString (&v); strlit"\n"]`;

val res = translate format_output_def;

(* Main wordfreq implementation *)

val wordfreq = process_topdecs`
  fun wordfreq u =
    case FileIO.inputLinesFrom (List.hd (Commandline.arguments()))
    of SOME lines =>
      print_list
        (List.map format_output
          (toAscList
            (List.foldl insert_line empty lines)))`;

val () = append_prog wordfreq;

(* Main wordfreq specification.
   Idea: for a given file_contents, the output of wordfreq should be the
   concatentation of format_output'd lines for a list of words ws and paired
   with their frequencies in file_contents. Which words? All the words in
   file_contents, in sorted order. Note that sorting by strict less-than means
   there are no duplicate words.

   We define valid_wordfreq_output so that
     valid_wordfreq_output file_contents output
   holds if output is valid for the file_contents, as described above.
*)

val valid_wordfreq_output_def = Define`
  valid_wordfreq_output file_contents output =
    ∃ws. set ws = set (all_words file_contents) ∧ SORTED $< ws ∧
         output = FLAT (MAP (λw. explode (format_output (w, frequency file_contents w))) ws)`;

(* Although we have defined valid_wordfreq_output as a relation between
   file_contents and output, it is actually functional (there is only one correct
   output). We prove this below: existence and uniqueness. *)

val valid_wordfreq_output_exists = Q.store_thm("valid_wordfreq_output_exists",
  `∃output. valid_wordfreq_output (implode file_chars) output`,
  rw[valid_wordfreq_output_def] \\
  qexists_tac`QSORT $<= (nub (all_words (implode file_chars)))` \\
  qmatch_goalsub_abbrev_tac`set l1 = LIST_TO_SET l2` \\
  `PERM (nub l2) l1` by metis_tac[QSORT_PERM] \\
  imp_res_tac PERM_LIST_TO_SET \\ fs[] \\
  simp[Abbr`l1`] \\
  match_mp_tac (MP_CANON ALL_DISTINCT_SORTED_WEAKEN) \\
  qexists_tac`$<=` \\ fs[mlstringTheory.mlstring_le_thm] \\
  conj_tac >- metis_tac[ALL_DISTINCT_PERM,all_distinct_nub] \\
  match_mp_tac QSORT_SORTED \\
  simp[transitive_def,total_def] \\
  metis_tac[mlstringTheory.mlstring_lt_trans,mlstringTheory.mlstring_lt_cases]);

val valid_wordfreq_output_unique = Q.store_thm("valid_wordfreq_output_unique",
  `∀out1 out2. valid_wordfreq_output s out1 ∧ valid_wordfreq_output s out2 ⇒ out1 = out2`,
  rw[valid_wordfreq_output_def] \\
  rpt AP_TERM_TAC \\
  match_mp_tac (MP_CANON SORTED_PERM_EQ) \\
  instantiate \\
  conj_asm1_tac >- (
    simp[transitive_def,antisymmetric_def] \\
    metis_tac[mlstringTheory.mlstring_lt_trans,
              mlstringTheory.mlstring_lt_antisym]) \\
  `ALL_DISTINCT ws ∧ ALL_DISTINCT ws'` by (
    conj_tac \\ match_mp_tac (GEN_ALL(MP_CANON SORTED_ALL_DISTINCT)) \\
    instantiate \\ simp[irreflexive_def] \\
    metis_tac[mlstringTheory.mlstring_lt_nonrefl] ) \\
  fs[ALL_DISTINCT_PERM_LIST_TO_SET_TO_LIST] \\
  metis_tac[PERM_TRANS,PERM_SYM]);

(* Now we can define a function that is the unique valid output for a given
   file_contents. Note that this function does not have a computable
   definition. So we cannot use it directly as our implementation.
   (translate wordfreq_output_spec_def will fail.)
*)

val wordfreq_output_spec_def =
  new_specification("wordfreq_output_spec_def",["wordfreq_output_spec"],
    GEN_ALL valid_wordfreq_output_exists |> SIMP_RULE std_ss [SKOLEM_THM]);

(* Now we state and prove a correctness theorem for the wordfreq program *)

val st = get_ml_prog_state();

(* These will be needed for xlet_auto to handle our use of List.foldl *)
val insert_line_v_thm = theorem"insert_line_v_thm";
val empty_v_thm = theorem"empty_v_thm" |> Q.GENL[`a`,`b`] |> Q.ISPECL[`NUM`,`STRING_TYPE`];
(* and this for our use of List.map *)
val format_output_v_thm = theorem"format_output_v_thm";

val wordfreq_spec = Q.store_thm("wordfreq_spec",
  (* TODO: write the specification for the wordfreq program *)
  (* hint: use wordfreq_output_spec to produce the desired output *)

(* The following proof sketch should work when you have roughly the right
   specification

   First, we use CF tactics to step through the wordfreq program propagating weakest preconditions generating verification
   *)

  strip_tac \\
  xcf"wordfreq" st \\

  (* TODO: step through the first few function calls in wordfreq using CF
     tactics like xlet_auto, xsimpl, xcon, etc. *)

  (* Before you step through the call to FileIO.inputLinesFrom, the following
     may be useful first to establish `wfcl cl`:
  *)
  reverse(Cases_on`wfcl cl`)
  >- (fs[mlcommandLineProgTheory.COMMANDLINE_def] \\ xpull \\ rfs[]) \\

  (* To get through the pattern match, try this: *)
  xmatch \\
  fs[ml_translatorTheory.OPTION_TYPE_def] \\
  reverse conj_tac >- (EVAL_TAC \\ simp[]) \\

  (* try xlet_auto and see that some of the specs for helper functions declared
     above might be helpful. You can add them to the assumptions like this: *)
  assume_tac insert_line_v_thm \\

  (* Second, after the CF part of the proof is finished, you should have a goal
     roughly of the form:
       STDOUT xxxx ==> STDOUT yyyy * GC
     the aim now is simply to show that xxxx = yyyy
     after which xsimpl will solve the goal
  *)

  (* TODO: extract some lemmas from the following? and turn it into holes and hints *)
  qmatch_goalsub_abbrev_tac`out ++ res` \\
  qmatch_goalsub_abbrev_tac`wordfreq_output_spec file_chars` \\
  `valid_wordfreq_output (implode file_chars) res` suffices_by (
    strip_tac \\
    `res = wordfreq_output_spec file_chars` by
      metis_tac[wordfreq_output_spec_def,valid_wordfreq_output_unique] \\
    xsimpl ) \\
  rw[Abbr`res`, valid_wordfreq_output_def] \\
  qmatch_asmsub_abbrev_tac`toAscList t` \\
  qmatch_asmsub_abbrev_tac`MAP format_output ls` \\
  qexists_tac`MAP FST ls` \\
  qspecl_then[`all_lines fs fname`,`empty`]mp_tac FOLDL_insert_line \\
  simp[empty_thm] \\
  impl_tac >- (
    simp[mlfileioProgTheory.all_lines_def,EVERY_MAP,mlstringTheory.implode_def,mlstringTheory.strcat_def] \\
    simp[EVERY_MEM] \\ metis_tac[mlstringTheory.explode_implode] ) \\
  strip_tac \\
  assume_tac mlstringTheory.good_cmp_compare \\ simp[Abbr`ls`] \\
  simp[MAP_FST_toAscList,mlstringTheory.mlstring_lt_def] \\
  simp[MAP_MAP_o,o_DEF] \\
  imp_res_tac MAP_FST_toAscList \\ fs[empty_thm] \\
  qmatch_goalsub_abbrev_tac`set (all_words w1) = set (all_words w2)` \\
  `all_words w1 = all_words w2` by (
    strip_assume_tac mlfileioProgTheory.concat_all_lines
    \\ simp[Abbr`w1`,Abbr`w2`]
    \\ `isSpace #"\n"` by EVAL_TAC
    \\ simp[all_words_concat_space] ) \\
  simp[] \\
  AP_TERM_TAC \\
  simp[MAP_EQ_f] \\
  simp[FORALL_PROD] \\ rw[] \\
  imp_res_tac MEM_toAscList \\
  rfs[GSYM lookup_thm] \\
  rename1`lookup compare w` \\
  first_x_assum(qspec_then`w`mp_tac) \\
  rw[Once lookup0_def] \\
  rw[frequency_def]);

(* Finally, we package the verified program up with the following boilerplate*)

val spec = wordfreq_spec |> SPEC_ALL |> UNDISCH_ALL |> add_basis_proj;
val name = "wordfreq"
val (sem_thm,prog_tm) = ioProgLib.call_thm (get_ml_prog_state ()) name spec
val wordfreq_prog_def = Define `wordfreq_prog = ^prog_tm`;

val wordfreq_semantics =
  sem_thm
  |> ONCE_REWRITE_RULE[GSYM wordfreq_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[rofsFFITheory.wfFS_def,rofsFFITheory.inFS_fname_def,PULL_EXISTS]
  |> Q.GEN`cls`
  |> SIMP_RULE(srw_ss())[mlcommandLineProgTheory.wfcl_def,AND_IMP_INTRO,GSYM CONJ_ASSOC,mlstringTheory.LENGTH_explode]
  |> curry save_thm "wordfreq_semantics";

val _ = export_theory();
