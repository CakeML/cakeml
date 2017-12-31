(*
  The CakeML program implementing the word frequency application.
  This is produced by a combination of translation and CF verification.
*)

open preamble basis
     splitwordsTheory balanced_mapTheory

(* note: opening all these theories/libraries can take a while
   and it will print many warning messages which can be ignored *)

val _ = new_theory "wordfreqProg";

val _ = translation_extends"basisProg";

(* Avoid printing potentially very long output *)
val _ = Globals.max_print_depth := 20

(* Pure functions for word frequency counting *)

val lookup0_def = Define`
  lookup0 w t = case lookup compare w t of NONE => 0n | SOME n => n`;

val lookup0_empty = Q.store_thm("lookup0_empty[simp]",
  `lookup0 w empty = 0`, EVAL_TAC);

val insert_word_def = Define`
  insert_word t w =
    insert compare w (lookup0 w t + 1) t`;

val insert_line_def = Define`
  insert_line t s =
     FOLDL insert_word t (splitwords s)`;

(* and their verification *)

val key_set_compare_unique = Q.store_thm("key_set_compare_unique[simp]",
  `key_set compare k = {k}`,
  rw[key_set_def,EXTENSION] \\
  metis_tac[TotOrd_compare,totoTheory.TotOrd]);

val IMAGE_key_set_compare_inj = Q.store_thm("IMAGE_key_set_compare_inj[simp]",
  `IMAGE (key_set compare) s1 = IMAGE (key_set compare) s2 ⇔ s1 = s2`,
  rw[EQ_IMP_THM]
  \\ fs[Once EXTENSION]
  \\ fs[EQ_IMP_THM] \\ rw[]
  \\ res_tac \\ fs[]);

val lookup0_insert = Q.store_thm("lookup0_insert",
  `invariant compare t ⇒
   lookup0 k (insert compare k' v t) =
   if k = k' then v else lookup0 k t`,
  rw[lookup0_def,lookup_insert,good_cmp_compare] \\
  metis_tac[TotOrd_compare,totoTheory.TotOrd]);

val insert_line_thm = Q.store_thm("insert_line_thm",
  `invariant compare t ∧
   insert_line t s = t'
   ⇒
   invariant compare t' ∧
   (∀w. lookup0 w t' =
        lookup0 w t + frequency s w) ∧
   FDOM (to_fmap compare t') = FDOM (to_fmap compare t) ∪ (IMAGE (key_set compare) (set (splitwords s)))`,
  strip_tac \\ rveq \\
  simp[insert_line_def,splitwords_def,frequency_def] \\
  Q.SPEC_TAC(`tokens isSpace s`,`ls`) \\
  ho_match_mp_tac SNOC_INDUCT \\ simp[] \\
  ntac 3 strip_tac \\
  simp[MAP_SNOC,FOLDL_SNOC,insert_word_def] \\
  rw[good_cmp_compare,insert_thm,FILTER_SNOC,lookup0_insert] \\
  rw[EXTENSION] \\ metis_tac[]);

val FOLDL_insert_line = Q.store_thm("FOLDL_insert_line",
  `∀ls t t' s.
    invariant compare t ∧ t' = FOLDL insert_line t ls ∧
    EVERY (λw. ∃x. w = strcat x (strlit "\n")) ls ∧
    s = concat ls
    ⇒
    invariant compare t' ∧
    (∀w. lookup0 w t' = lookup0 w t + frequency s w) ∧
    FDOM (to_fmap compare t') = FDOM (to_fmap compare t) ∪ IMAGE (key_set compare) (set (splitwords s))`,
  Induct \\ simp[concat_nil,concat_cons] \\ ntac 3 strip_tac \\
  rename1`insert_line t w` \\
  imp_res_tac insert_line_thm \\ fs[] \\
  `strlit "\n" = str #"\n"` by EVAL_TAC \\
  `isSpace #"\n"` by EVAL_TAC \\
  first_x_assum drule \\
  rw[frequency_concat,splitwords_concat,frequency_concat_space,splitwords_concat_space] \\
  rw[EXTENSION] \\ metis_tac[]);

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
val res = translate (insert_line_def |> REWRITE_RULE[splitwords_def]);

val format_output_def = Define`
  format_output (k,v) = concat [k; strlit": "; toString (&v); strlit"\n"]`;

val res = translate format_output_def;

val compute_wordfreq_output_def = Define `
  compute_wordfreq_output input_lines =
    MAP format_output (toAscList (FOLDL insert_line empty input_lines))`

val res = translate compute_wordfreq_output_def;

(* Main wordfreq implementation *)

val wordfreq = process_topdecs`
  fun wordfreq u =
    case TextIO.inputLinesFrom (List.hd (CommandLine.arguments()))
    of SOME lines =>
      TextIO.print_list (compute_wordfreq_output lines)`;

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
    ∃ws. set ws = set (splitwords file_contents) ∧ SORTED $< ws ∧
         output = concat (MAP (λw. format_output (w, frequency file_contents w)) ws)`;

(* Although we have defined valid_wordfreq_output as a relation between
   file_contents and output, it is actually functional (there is only one correct
   output). We prove this below: existence and uniqueness. *)

val valid_wordfreq_output_exists = Q.store_thm("valid_wordfreq_output_exists",
  `∃output. valid_wordfreq_output file_chars output`,
  rw[valid_wordfreq_output_def] \\
  qexists_tac`QSORT $<= (nub (splitwords file_chars))` \\
  qmatch_goalsub_abbrev_tac`set l1 = LIST_TO_SET l2` \\
  `PERM (nub l2) l1` by metis_tac[QSORT_PERM] \\
  imp_res_tac PERM_LIST_TO_SET \\ fs[] \\
  simp[Abbr`l1`] \\
  match_mp_tac (MP_CANON ALL_DISTINCT_SORTED_WEAKEN) \\
  qexists_tac`$<=` \\ fs[mlstring_le_thm] \\
  conj_tac >- metis_tac[ALL_DISTINCT_PERM,all_distinct_nub] \\
  match_mp_tac QSORT_SORTED \\
  simp[transitive_def,total_def] \\
  metis_tac[mlstring_lt_trans,mlstring_lt_cases]);

val valid_wordfreq_output_unique = Q.store_thm("valid_wordfreq_output_unique",
  `∀out1 out2. valid_wordfreq_output s out1 ∧ valid_wordfreq_output s out2 ⇒ out1 = out2`,
  rw[valid_wordfreq_output_def] \\
  rpt AP_TERM_TAC \\
  match_mp_tac (MP_CANON SORTED_PERM_EQ) \\
  instantiate \\
  conj_asm1_tac >- (
    simp[transitive_def,antisymmetric_def] \\
    metis_tac[mlstring_lt_trans, mlstring_lt_antisym]) \\
  `ALL_DISTINCT ws ∧ ALL_DISTINCT ws'` by (
    conj_tac \\ match_mp_tac (GEN_ALL(MP_CANON SORTED_ALL_DISTINCT)) \\
    instantiate \\ simp[irreflexive_def] \\
    metis_tac[mlstring_lt_nonrefl] ) \\
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

(* The following lemmas establish a connection between the expected output of
   the wordfreq program and our desired semantics, wordfreq_output_spec. (The
   statement of this lemma was obtained by trying to do the wordfreq_spec proof
   below and seeing where it ended up. You can skip forward to do that first if
   you like.)
*)

val wordfreq_output_valid = Q.store_thm("wordfreq_output_valid",
  `!file_contents.
     valid_wordfreq_output file_contents
       (concat (compute_wordfreq_output (lines_of file_contents)))`,
  rw[valid_wordfreq_output_def,compute_wordfreq_output_def] \\
  qmatch_goalsub_abbrev_tac`MAP format_output ls` \\
  (* EXERCISE: what is the list of words to use here? *)
  (* hint: toAscList returns a list of pairs, and you can use
           MAP FST ls and MAP SND ls to obtain lists of the first/second items
           of these pairs *)
  (* qexists_tac `<put your answer here>` \\ *)
  (* Now we use the theorem about insert_line proved earlier *)
  qspecl_then[`lines_of file_contents`,`empty`]mp_tac FOLDL_insert_line \\
  simp[empty_thm] \\
  impl_tac >- (
    simp[lines_of_def,EVERY_MAP,implode_def,strcat_def] \\
    simp[EVERY_MEM] \\ metis_tac[explode_implode] ) \\
  strip_tac \\
  assume_tac good_cmp_compare \\ simp[Abbr`ls`] \\
  (* simplify the remaining goal using properties of toAscList etc. *)
  simp[MAP_FST_toAscList,mlstring_lt_def] \\
  simp[MAP_MAP_o,o_DEF] \\
  imp_res_tac MAP_FST_toAscList \\ fs[empty_thm] \\
  qmatch_goalsub_abbrev_tac`set (splitwords w1) = set (splitwords w2)` \\
  `splitwords w1 = splitwords w2` by (
    qspec_then `file_contents` strip_assume_tac concat_lines_of
    \\ simp[Abbr`w1`,Abbr`w2`]
    \\ `isSpace #"\n"` by EVAL_TAC
    \\ simp[splitwords_concat_space] ) \\
  simp[] \\
  AP_TERM_TAC \\
  simp[MAP_EQ_f] \\
  simp[FORALL_PROD] \\ rw[] \\
  (* EXERCISE: finish the proof *)
  (* hint: try DB.match [] ``MEM _ (toAscList _)`` *)
  (* hint: also consider using lookup_thm *)
  (* hint: the following idiom is useful for specialising an assumption:
     first_x_assum (qspec_then `<insert specialisation here>` mp_tac) *)
);

val wordfreq_output_spec_unique = Q.store_thm("wordfreq_output_spec_unique",
  `valid_wordfreq_output file_chars output ⇒
   wordfreq_output_spec file_chars = output`,
  (* EXERCISE: prove this *)
  (* hint: it's a one-liner *)
);

(* These will be needed for xlet_auto to handle our use of List.foldl *)
val insert_line_v_thm = theorem"insert_line_v_thm";
val empty_v_thm = theorem"empty_v_thm" |> Q.GENL[`a`,`b`] |> Q.ISPECL[`STRING_TYPE`,`NUM`];
(* and this for our use of List.map *)
val format_output_v_thm = theorem"format_output_v_thm";

val wordfreq_spec = Q.store_thm("wordfreq_spec",
  (* EXERCISE: write the specification for the wordfreq program *)
  (* hint: it should be very similar to wordcount_spec (in wordcountProgScript.sml) *)
  (* hint: use wordfreq_output_spec to produce the desired output *)

(* The following proof sketch should work when you have roughly the right
   specification

   First, we use CF tactics to step through the wordfreq program propagating weakest preconditions generating verification
   *)

  strip_tac \\
  xcf"wordfreq" (get_ml_prog_state()) \\

  (* EXERCISE: step through the first few function calls in wordfreq using CF
     tactics like xlet_auto, xsimpl, xcon, etc. *)

  (* Before you step through the call to TextIO.inputLinesFrom, the following
     may be useful first to establish `wfcl cl`, which constrains fname to be
     a valid filename:
  *)
  reverse(Cases_on`wfcl cl`)
  >- (fs[COMMANDLINE_def] \\ xpull \\ rfs[]) \\

  (* To get through the pattern match, try this: *)
  xmatch \\
  fs[OPTION_TYPE_def] \\
  (* this part solves the validate_pat conjunct *)
  reverse conj_tac >- (EVAL_TAC \\ simp[]) \\

  xlet_auto >- xsimpl \\

  (* hint: when xlet_auto is no longer applicable, you can use other CF tactics like xapp *)

  (* After the CF part of the proof is finished, you should have a goal
     roughly of the form:
       STDIO (add_stdout _ xxxx) ==>> STDIO (add_stdout _ yyyy) * GC
     the aim now is simply to show that xxxx = yyyy
     after which xsimpl will solve the goal.
     We can make this aim explicit as follows:
  *)
  qmatch_abbrev_tac`STDIO (add_stdout _ xxxx) ==>> STDIO (add_stdout _ yyyy)* GC` \\
  `xxxx = yyyy` suffices_by xsimpl \\
  (* now let us unabbreviate xxxx and yyyy *)
  map_every qunabbrev_tac[`xxxx`,`yyyy`] \\ simp[] \\

  (* EXERCISE: use the lemmas above to finish the proof, see also all_lines_def *)
);

(* Finally, we package the verified program up with the following boilerplate *)

val wordfreq_whole_prog_spec = Q.store_thm("wordfreq_whole_prog_spec",
  `hasFreeFD fs ∧ inFS_fname fs (File fname) ∧
   cl = [pname; fname] ∧
   contents = implode (THE (ALOOKUP fs.files (File fname)))
   ⇒
   whole_prog_spec ^(fetch_v "wordfreq" (get_ml_prog_state())) cl fs
         ((=) (add_stdout fs (wordfreq_output_spec contents)))`,
  disch_then assume_tac
  \\ simp[whole_prog_spec_def]
  \\ qmatch_goalsub_abbrev_tac`fs1 = _ with numchars := _`
  \\ qexists_tac`fs1`
  \\ simp[Abbr`fs1`,GSYM add_stdo_with_numchars,with_same_numchars]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe (UNDISCH wordfreq_spec)))
  \\ xsimpl);

val (sem_thm,prog_tm) = whole_prog_thm (get_ml_prog_state ()) "wordfreq" (UNDISCH wordfreq_whole_prog_spec)
val wordfreq_prog_def = Define `wordfreq_prog = ^prog_tm`;

val wordfreq_semantics =
  sem_thm |> ONCE_REWRITE_RULE[GSYM wordfreq_prog_def]
  |> DISCH_ALL |> Q.GENL[`cl`,`contents`]
  |> SIMP_RULE(srw_ss())[AND_IMP_INTRO,GSYM CONJ_ASSOC]
  |> curry save_thm "wordfreq_semantics";

val _ = export_theory();
