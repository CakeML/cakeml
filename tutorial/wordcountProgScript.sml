(*
  Simple wordcount program, to demonstrate use of CF.
*)

open preamble
     ml_translatorLib cfTacticsLib
     basisProgTheory basisFunctionsLib ioProgLib
     cfLetAutoLib

val _ = new_theory"wordcountProg";

val _ = translation_extends"basisProg";

(* TODO: move *)
val FLAT_MAP_TOKENS_FIELDS = Q.store_thm("FLAT_MAP_TOKENS_FIELDS",
  `∀P' ls P.
    (∀x. P' x ⇒ P x) ⇒
     FLAT (MAP (TOKENS P) (FIELDS P' ls)) =
     TOKENS P ls`,
  Induct_on`FIELDS P' ls` \\ rw[] \\
  qpat_x_assum`_ = FIELDS _ _`(assume_tac o SYM) \\
  imp_res_tac FIELDS_next \\
  Cases_on`LENGTH ls ≤ LENGTH h` >- (
    imp_res_tac FIELDS_full \\ fs[] ) \\
  fs[] \\ rw[] \\
  fs[IS_PREFIX_APPEND,DROP_APPEND,DROP_LENGTH_TOO_LONG,ADD1] \\
  `h ++ [c] ++ l  = h ++ (c::l)` by simp[] \\ pop_assum SUBST_ALL_TAC \\
  asm_simp_tac std_ss [TOKENS_APPEND]);
(* -- *)

(* TODO: re-use this in wordfreq. N.B. a lot of this is currently copied *)
val all_words_def = Define`
  all_words s = tokens isSpace s`;

val all_words_nil = Q.store_thm("all_words_nil[simp]",
  `all_words (implode "") = []`, EVAL_TAC);

val all_words_concat = Q.store_thm("all_words_concat",
  `isSpace sp ⇒
   all_words (s1 ^ str sp ^ s2) = all_words s1 ++ all_words s2`,
  rw[all_words_def,mlstringTheory.tokens_append,mlstringTheory.strcat_assoc]);

val all_words_concat_space = Q.store_thm("all_words_concat_space",
  `isSpace sp ⇒ all_words (s1 ^ str sp) = all_words s1`,
  rw[] \\ qspec_then`implode ""`mp_tac(Q.GEN`s2`all_words_concat) \\
  fs[mlstringTheory.strcat_def]);

val all_words_all_lines = Q.store_thm("all_words_all_lines",
  `FLAT (MAP all_words (all_lines fs fname)) =
   all_words (implode (THE (ALOOKUP fs.files fname)))`,
  `isSpace #"\n"` by EVAL_TAC \\
  rw[mlfileioProgTheory.all_lines_def,MAP_MAP_o,o_DEF,
     GSYM mlstringTheory.str_def,all_words_concat_space] \\
  rw[all_words_def,mlstringTheory.TOKENS_eq_tokens_sym] \\
  srw_tac[ETA_ss][GSYM o_DEF,GSYM MAP_MAP_o] \\
  simp[GSYM MAP_FLAT] \\ AP_TERM_TAC \\
  qspec_tac(`THE (ALOOKUP fs.files fname)`,`ls`) \\
  rw[splitlines_def]
  >- (
    qmatch_asmsub_abbrev_tac`NULL (LAST l)` \\
    Q.ISPEC_THEN`l`mp_tac APPEND_FRONT_LAST \\
    impl_tac >- rw[Abbr`l`] \\
    fs[NULL_EQ] \\ strip_tac \\
    `FLAT (MAP (TOKENS isSpace) (FRONT l)) = FLAT (MAP (TOKENS isSpace) l)` by (
      pop_assum(fn th => CONV_TAC(RAND_CONV(DEPTH_CONV(REWR_CONV(SYM th))))) \\
      simp[] \\ EVAL_TAC ) \\
    simp[Abbr`l`] \\
    match_mp_tac FLAT_MAP_TOKENS_FIELDS \\
    rw[] \\ EVAL_TAC ) \\
  match_mp_tac FLAT_MAP_TOKENS_FIELDS \\
  rw[] \\ EVAL_TAC);
(* -- *)

val wc_lines_def = Define`
  wc_lines lines = SUM (MAP (LENGTH o all_words) lines)`;

val res = translate all_words_def;
val res = translate wc_lines_def;

val wordcount = process_topdecs`
  fun wordcount u =
    case FileIO.inputLinesFrom (List.hd (Commandline.arguments()))
    of SOME lines =>
      (print (Int.toString (wc_lines lines)); print " ";
       print (Int.toString (List.length lines)); print "\n")`;
val _ = append_prog wordcount;

val wordcount_spec = Q.store_thm("wordcount_spec",
  `wfFS fs ∧ (* TODO: encapsulate these *)
   CARD (FDOM (alist_to_fmap fs.infds)) < 255 ∧

   inFS_fname fs fname ∧
   cl = [explode pname; explode fname] ∧
   contents = THE (ALOOKUP fs.files fname)
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "wordcount" (get_ml_prog_state()))
     [uv] (COMMANDLINE cl * ROFS fs * STDOUT out)
     (POSTv uv. &UNIT_TYPE () uv * ROFS fs * COMMANDLINE cl *
                 STDOUT (out ++ (toString (LENGTH (TOKENS isSpace contents))) ++ " " ++
                                (toString (LENGTH (splitlines contents)) ++ "\n")))`,
  strip_tac \\
  xcf "wordcount" (get_ml_prog_state()) \\
  xlet_auto >- (xcon \\ xsimpl) \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  reverse(Cases_on`wfcl cl`) >- (rfs[mlcommandLineProgTheory.COMMANDLINE_def] \\ xpull) \\
  `FILENAME fname fnamev` by ( (* TODO: nicer? *)
    rfs[mlfileioProgTheory.FILENAME_def,
        mlcommandLineProgTheory.wfcl_def,commandLineFFITheory.validArg_def,
        EVERY_MEM,mlstringTheory.LENGTH_explode] ) \\
  xlet_auto >- (xsimpl \\ fs[]) \\
  xmatch \\ fs[ml_translatorTheory.OPTION_TYPE_def] \\
  reverse conj_tac >- (EVAL_TAC \\ fs[]) \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  xlet_auto >- ( (* TODO: nicer? *)
    xsimpl \\
    CONV_TAC SWAP_EXISTS_CONV \\
    qexists_tac`out` \\ xsimpl ) \\
  xlet_auto >- ( (* TODO: nicer? *)
    xsimpl \\
    CONV_TAC SWAP_EXISTS_CONV \\
    qexists_tac`out` \\ xsimpl ) \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  xlet_auto >- ( (* TODO: nicer? *)
    xsimpl \\
    CONV_TAC SWAP_EXISTS_CONV \\
    qexists_tac`out` \\ xsimpl ) \\
  xapp \\ xsimpl \\ (* TODO: same issue with xapp as above? *)
  qmatch_goalsub_abbrev_tac`STDOUT output` \\
  CONV_TAC SWAP_EXISTS_CONV \\
  qexists_tac`output` \\ xsimpl \\
  qmatch_goalsub_abbrev_tac`STDOUT (output'++"\n") * GC` \\
  `output = output'` suffices_by xsimpl \\
  simp[Abbr`output`,Abbr`output'`] \\
  simp[wc_lines_def] \\
  qmatch_abbrev_tac`s1 ++ " " ++ s2 = t1 ++ " " ++ t2` \\
  `s1 = t1 ∧ s2 = t2` suffices_by rw[] \\
  simp[Abbr`s1`,Abbr`t1`,Abbr`s2`,Abbr`t2`] \\
  simp[mlintTheory.toString_thm,integerTheory.INT_ABS_NUM] \\
  reverse conj_tac >- simp[mlfileioProgTheory.all_lines_def] \\
  simp[GSYM MAP_MAP_o,GSYM LENGTH_FLAT,all_words_all_lines] \\
  simp[all_words_def,mlstringTheory.TOKENS_eq_tokens_sym]);

val spec = wordcount_spec |> UNDISCH_ALL |> add_basis_proj
val name = "wordcount"
val (sem_thm,prog_tm) = call_thm (get_ml_prog_state()) name spec

val wordcount_prog_def = mk_abbrev"wordcount_prog" prog_tm;

val wordcount_semantics = save_thm("wordcount_semantics",
  sem_thm
  |> PURE_REWRITE_RULE[GSYM wordcount_prog_def]
  |> DISCH_ALL
  |> Q.GENL[`cls`,`contents`]
  |> SIMP_RULE(srw_ss())[]
  |> SIMP_RULE std_ss [AND_IMP_INTRO]);

(* Ramana's approx time spent on this:
   20 mins setting up the definitions and starting the proof
   30 mins debugging xlet_auto
   10 mins working towards the core of the proof
   30 mins on core proof (including spec tweaking. and aux. lemmas)
*)

val _ = export_theory();
