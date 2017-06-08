(*
  The CakeML program implementing the word frequency application.
  This is produced by a combination of translation and CF verification.
*)

open preamble
     ml_translatorLib cfTacticsLib basisFunctionsLib cfLetAutoLib
     ioProgLib basisProgTheory
     wordfreqTheory

(* TODO: simplify the required includes (translator, basis, CF) for such examples *)

val _ = new_theory "wordfreqProg";

val _ = translation_extends"basisProg";

(* TODO: move *)
val ALL_DISTINCT_SORTED_WEAKEN = Q.store_thm("ALL_DISTINCT_SORTED_WEAKEN",
  `∀R R' ls. (∀x y. MEM x ls ∧ MEM y ls ∧ x ≠ y ⇒ (R x y ⇔ R' x y)) ∧
        ALL_DISTINCT ls ∧ SORTED R ls ⇒ SORTED R' ls`,
  gen_tac \\ ho_match_mp_tac SORTED_IND \\ rw[]
  \\ pop_assum mp_tac
  \\ simp_tac(srw_ss())[SORTED_DEF]
  \\ metis_tac[]);
(* -- *)

(* avoid printing potentially very long output *)
val _ = Globals.max_print_depth := 20

(* TODO:
  given that this is also used in grep,
  should we include it in the basis? *)

val res = translate balanced_mapTheory.lookup_def;
val res = translate balanced_mapTheory.singleton_def;
val res = translate balanced_mapTheory.ratio_def;
val res = translate balanced_mapTheory.size_def;
val res = translate balanced_mapTheory.delta_def;
val res = translate balanced_mapTheory.balanceL_def;
val res = translate balanced_mapTheory.balanceR_def;
val res = translate balanced_mapTheory.insert_def;
val res = translate balanced_mapTheory.empty_def;
val res = translate balanced_mapTheory.foldrWithKey_def;
val _ = next_ml_names := ["toAscList"];
val res = translate balanced_mapTheory.toAscList_def;

val res = translate lookup0_def;
val res = translate insert_word_def;
val res = translate insert_line_def;

(* TODO: possible extension: pad the word so the colons will line up *)
val format_output_def = Define`
  format_output (k,v) = concat [k; strlit": "; toString (&v); strlit"\n"]`;
val res = translate format_output_def;

(* TODO: explain process_topdecs, CakeML syntax etc.
         but actually this should be covered by the wordcount example *)

(* TODO: do something like this as an exercise?

(* An imperative higher-order function for applying a function to every element
   in a bst in order *)

val app_in_order = process_topdecs`
  fun app_in_order f t =
  case t of
    Tip => ()
  | Bin (_,k,v,l,r) =>
      (f k v; app_in_order f l; app_in_order f r)`;
val () = append_prog app_in_order;

(*
val app_in_order_spec = Q.store_thm("app_in_order_spec",
  `BALANCED_MAP_BALANCED_MAP_TYPE kty vty t tv ∧
   (∀n kv vv.
      n < LENGTH (toAscList t) ∧
      kty (FST (EL n (toAscList t))) kv ∧
      vty (SND (EL n (toAscList t))) vv
      ⇒
        app p fv [kv; vv] (P (TAKE n (toAscList t)))
          (POSTv uv. &UNIT_TYPE () uv * P (TAKE (n+1) (toAscList t))))
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"app_in_order"(get_ml_prog_state())) [fv; tv]
     (P [])
     (POSTv uv. &UNIT_TYPE () uv *
                P (toAscList t))`,
  rw[] \\
  Induct_on`t`
*)

*)

(* TODO: how do you debug a definition like this that fails to process?
I tried processing one internal declaration at a time (deleting the others)
val wordfreq = process_topdecs`
  fun wordfreq _ =
    let
      val filename = List.hd (Commandline.arguments())
      val fd = FileIO.openIn filename
      fun loop t =
        case FileIO.inputLine fd of NONE => t
           | SOME line => insert_line t line
      val t = loop empty
      val _ = FileIO.close fd
      fun print_output k v = print (format_output k v)
    in
      app_in_order print_output t
    end`;

n.b. this is extra hard with missing/invalid definitions (like "empty" and
"toAscList", which were not originally translated) so that even if it  parses it
might lead to bad CF errors later
*)

val wordfreq = process_topdecs`
  fun wordfreq u =
    case FileIO.inputLinesFrom (List.hd (Commandline.arguments()))
    of SOME lines =>
      (* TODO: add o to mlbasicsProg? *)
      List.app (fn x => print (format_output x))
        (toAscList (List.foldl insert_line empty lines))`;

val () = append_prog wordfreq;

(* Now we state and prove a correctness theorem for the wordfreq program *)

val st = get_ml_prog_state();

(* TODO: this is wrong (because all_words gives duplicates)
   leave it as an exercises to see why this spec is wrong?
val valid_wordfreq_output_def = Define`
  valid_wordfreq_output file_contents output =
    ∃ls. PERM ls (all_words file_contents) ∧ SORTED $<= ls ∧
         output = FLAT (MAP (λw. explode (format_output (w, frequency file_contents w))) ls)`;
*)

val valid_wordfreq_output_def = Define`
  valid_wordfreq_output file_contents output =
    ∃ws. set ws = set (all_words file_contents) ∧ SORTED $< ws ∧
         output = FLAT (MAP (λw. explode (format_output (w, frequency file_contents w))) ws)`;

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

val wordfreq_output_spec_def =
  new_specification("wordfreq_output_spec_def",["wordfreq_output_spec"],
    GEN_ALL valid_wordfreq_output_exists |> SIMP_RULE std_ss [SKOLEM_THM]);

(* TODO: explain p:'ffi ffi_proj, or make it simpler *)
(* TODO: explain antiquotation (^) *)

val wordfreq_spec = Q.store_thm("wordfreq_spec",
  `wfFS fs ∧ CARD (set (MAP FST fs.infds)) < 255 (* TODO: this should be part of wfFS, and possibly both part of ROFS *)
   ∧ inFS_fname fs fname ∧ cl = [explode pname; explode fname]
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "wordfreq" st) [Conv NONE []]
     (COMMANDLINE cl * ROFS fs * STDOUT out)
     (POSTv uv.
       &UNIT_TYPE () uv *
       COMMANDLINE cl * ROFS fs * STDOUT (out ++ wordfreq_output_spec (THE (ALOOKUP fs.files fname))))`,
  strip_tac \\
  xcf"wordfreq" st \\
  xlet_auto >- (xcon \\ xsimpl) \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  (* TODO: xlet_auto should work here, leaving the FILENAME condition to be proved *)
  reverse(Cases_on`wfcl cl`) >- (fs[mlcommandLineProgTheory.COMMANDLINE_def] \\ xpull \\ rfs[]) \\
  rfs[mlcommandLineProgTheory.wfcl_def] \\
  rename1`STRING_TYPE fname fv` \\
  `FILENAME fname fv` by
    fs[mlfileioProgTheory.FILENAME_def,
      commandLineFFITheory.validArg_def,
      mlstringTheory.LENGTH_explode,EVERY_MEM] \\
  xlet_auto >- xsimpl \\
  xmatch \\
  fs[ml_translatorTheory.OPTION_TYPE_def] \\
  reverse conj_tac >- (EVAL_TAC \\ simp[]) \\
  (* try xlet_auto to see that these specs are needed *)
  assume_tac (theorem"insert_line_v_thm") \\
  assume_tac (theorem"empty_v_thm" |> Q.GENL[`a`,`b`] |> Q.ISPECL[`NUM`,`STRING_TYPE`]) \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  (* TODO: it would be nice for xlet_auto to tell you when a spec is not found
           (but xapp needs to do this too) *)
  (* TODO: this is terrible.. *)
  xfun_spec`pf`
    `∀pr pv out.
     PAIR_TYPE STRING_TYPE NUM pr pv ⇒
     app p pf [pv] (STDOUT out) (POSTv uv. &UNIT_TYPE () uv * STDOUT (out ++ explode (format_output pr)))`
  >- (
    rw[] \\
    first_x_assum match_mp_tac \\
    xlet_auto >- xsimpl \\
    xapp \\ xsimpl ) \\
  xapp_spec
  (mllistProgTheory.app_spec
   |> CONV_RULE(RESORT_FORALL_CONV List.rev)
   |> Q.ISPEC`PAIR_TYPE STRING_TYPE NUM`) \\
  instantiate \\
  CONV_TAC SWAP_EXISTS_CONV \\
  qmatch_assum_abbrev_tac`LIST_TYPE _ ls _` \\
  (*
  qexists_tac`λn. STDOUT (out ++ FLAT (TAKE n (MAP (explode o format_output) ls)))` \\
  xsimpl \\
  conj_tac >- (
    rw[] \\
    Q.ISPEC_THEN`ls`FULL_STRUCT_CASES_TAC SNOC_CASES \\
    fs[TAKE_SNOC,GSYM MAP_TAKE] \\
  *)
  cheat);

(* partial old version without help from inputLinesFrom

val wordfreq = process_topdecs`
  fun wordfreq u =
    let
      val filename = List.hd (Commandline.arguments())
      val fd = FileIO.openIn filename
      fun loop t =
        case FileIO.inputLine fd of NONE => t
           | SOME line => insert_line t line
      val t = loop empty
      val u = FileIO.close fd
    in
      List.app (print o format_output) (toAscList t)
    end`;

(* TODO:
   this is the spec I originally devised, but it doesn't work with ioProgLib.call_thm
   could ioProgLib.call_thm be made more robust for that?
   (but note since this isn't proved, it is probably wrong)
val wordfreq_spec = Q.store_thm("wordfreq_spec",
  `EVERY validArg cl ∧
   LENGTH cl > 1 ∧ SUM (MAP LENGTH cl) + LENGTH cl < 257 ∧
   fname = implode (EL 1 cl) ∧
   inFS_fname fs fname ∧
   wfFS fs
   ⇒ app (p:'ffi ffi_proj) ^(fetch_v "wordfreq" st) [Conv NONE []]
       (COMMANDLINE cl * ROFS fs * STDOUT out)
       (POSTv uv.
        &UNIT_TYPE () uv * COMMANDLINE cl * ROFS fs *
        (SEP_EXISTS out'.
           STDOUT (out ++ out') *
           &valid_wordfreq_output (THE (ALOOKUP fs.files fname)) out'))`,
  strip_tac \\
  xcf "wordfreq" st \\
  cheat);
*)

val wordfreq_spec = Q.store_thm("wordfreq_spec",
  `inFS_fname fs fname ∧ cl = MAP explode [pname; fname] ∧
   wfFS fs ∧ CARD (set (MAP FST fs.infds)) < 255 (* TODO: this should be part of wfFS *)
   ⇒ app (p:'ffi ffi_proj) ^(fetch_v "wordfreq" st) [Conv NONE []]
       (* TODO: Magnus suggests wfFS should be part of ROFS *)
       (COMMANDLINE cl * ROFS fs * STDOUT out * STDERR err)
       (POSTv uv.
        &UNIT_TYPE () uv *
        (SEP_EXISTS out' err'.
           &(∃ls.
               out' = out ++ ls ∧
               valid_wordfreq_output
                 (implode (THE (ALOOKUP fs.files fname))) ls ∧
               err' = err) *
           STDOUT out' * STDERR err') *
        (COMMANDLINE cl * ROFS fs))`,
  strip_tac \\
  xcf "wordfreq" st \\
  xlet_auto >- (xcon \\ xsimpl) \\
  xlet_auto >- xsimpl \\
  (* try xlet_auto to see what is needed *)
  reverse(Cases_on`wfcl cl`) >- (fs[mlcommandLineProgTheory.COMMANDLINE_def] \\ xpull \\ rfs[]) \\
  `[fname] <> []` by (rfs[]) \\
  xlet_auto >- xsimpl \\
  (* try xlet_auto to see what is needed *)
  rename1`STRING_TYPE fname fv` \\
  `FILENAME fname fv`
    by rfs[mlfileioProgTheory.FILENAME_def,
           mlcommandLineProgTheory.wfcl_def,
           mlstringTheory.LENGTH_explode,
           commandLineFFITheory.validArg_def,EVERY_MEM] \\
  xlet_auto
  >- xsimpl
  >- (xsimpl \\ rw[]) \\
  xfun_spec`loop`
    `∀t tv fd fs fdv.
      validFD fd fs ∧ WORD ((n2w fd):word64) fdv ∧
      BALANCED_MAP_BALANCED_MAP_TYPE STRING_TYPE NUM t tv ∧
      invariant compare t
      ⇒
      app p loop [tv] (ROFS fs) (POSTv tv'.
        &(∃t'. BALANCED_MAP_BALANCED_MAP_TYPE STRING_TYPE NUM t' tv' ∧ invariant compare t' ∧
               (∀w. lookup0 w t' = lookup0 w t + SUM (MAP (λln. frequency (implode ln) w) (linesFD fd fs))))
        * ROFS (bumpAllFD fd fs))`
  >- (
    Induct_on`linesFD fd fs`
    >- (
      rpt gen_tac \\
      disch_then(assume_tac o SYM) \\
      fs[GSYM rofsFFITheory.FDline_NONE_linesFD] \\
      rw[] \\ first_x_assum match_mp_tac \\
      qpat_x_assum`WORD (n2w (nextFD _)) _`kall_tac \\
      `validFD (w2n ((n2w fd):word64)) fs'` by fs[w2n_n2w,WORD_def]

      qhdtm_x_assum`WORD`kall_tac \\
      `∃fdv. WORD ((n2w fd):word64) fdv` by ( simp[WORD_def] ) \\
      m``w2n (n2w _)``
      xlet_auto

      >- (
        xsimpl
        f"nextfd"
        f"inputline"
  cheat);
*)

val spec = wordfreq_spec |> SPEC_ALL |> UNDISCH_ALL |> add_basis_proj;
val name = "wordfreq"
val (sem_thm,prog_tm) = ioProgLib.call_thm (get_ml_prog_state ()) name spec
val wordfreq_prog_def = Define `wordfreq_prog = ^prog_tm`;

(* TODO:
  want a way to print this program out as concrete syntax (to be fed
  into the bootstrapped compiler for example) *)

val wordfreq_semantics =
  sem_thm
  |> ONCE_REWRITE_RULE[GSYM wordfreq_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[rofsFFITheory.wfFS_def,rofsFFITheory.inFS_fname_def,PULL_EXISTS]
  |> Q.GEN`cls`
  |> SIMP_RULE(srw_ss())[mlcommandLineProgTheory.wfcl_def,AND_IMP_INTRO,GSYM CONJ_ASSOC,mlstringTheory.LENGTH_explode]
  |> curry save_thm "wordfreq_semantics";

val _ = export_theory();
