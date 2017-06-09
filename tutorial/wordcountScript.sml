(*
  Simple wordcount program, to demonstrate use of CF.
*)

open preamble
     ml_translatorLib cfTacticsLib
     basisProgTheory basisFunctionsLib
     cfLetAutoLib

val _ = new_theory"wordcount";

val _ = translation_extends"basisProg";

(* TODO: re-use this in wordfreq? *)
val all_words_def = Define`
  all_words s = tokens isSpace s`;
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
                                (toString (LENGTH (TOKENS ((=)#"\n") contents)) ++ "\n")))`,
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
  xapp \\ xsimpl \\
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
  cheat (* TODO: prove lemmas about all_lines and all_words *));

(* Ramana's time spent on this so far:
   20 mins setting up the definitions and starting the proof
   30 mins debugging xlet_auto
   10 mins working towards the core of the proof
*)

val _ = export_theory();
