(*
  grep example: search for file lines matching a regular expression.
*)
open preamble basis
     charsetTheory regexpTheory regexp_parserTheory regexp_compilerTheory

val _ = new_theory "grepProg";

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

(* TODO: translate balanced_map module separately? *)
val _ = ml_translatorLib.pick_name :=
  let val default = !ml_translatorLib.pick_name in
    fn c =>
    if same_const c ``balanced_map$member`` then "balanced_map_member" else
    if same_const c ``balanced_map$empty`` then "balanced_map_empty" else
      default c
  end

val spec64 = INST_TYPE[alpha|->``:64``]
val _ = translate(word_bit_test |> spec64);

val _ = translate (charsetTheory.charset_full_def |> CONV_RULE (RHS_CONV EVAL));
val _ = translate charset_mem_def;

val _ = register_type``:regexp``;

(* check regexp is known to be an EqualityType *)
val EqualityType_regexp = EqualityType_rule [] ``:regexp``;

(* The following is a translation of balanced_map. The translation of
   balanced_map from basis cannot be used here beause the basis only
   exposes the mlmapTheory functions which provide a neater -- but
   different -- interface. The duplication doesn't matter due to
   flat_elim removing all the unused functions during compilation. *)

val _ = translate balanced_mapTheory.size_def;
val _ = translate balanced_mapTheory.singleton_def;
val _ = translate balanced_mapTheory.ratio_def;
val _ = translate balanced_mapTheory.delta_def;
val _ = translate balanced_mapTheory.balanceL_def;
val _ = translate balanced_mapTheory.balanceR_def;
val _ = translate balanced_mapTheory.deleteFindMax_def;

val deleteFindmax_side_thm = Q.prove (
  `!m. m ≠ Tip ⇒ deletefindmax_1_side m`,
  ho_match_mp_tac balanced_mapTheory.deleteFindMax_ind >>
  ONCE_REWRITE_TAC [theorem "deletefindmax_1_side_def"] >>
  rw [] >>
  ONCE_REWRITE_TAC [theorem "deletefindmax_1_side_def"] >>
  rw [] >>
  metis_tac []) |> update_precondition;

val _ = translate balanced_mapTheory.deleteFindMin_def;

val deleteFindmin_side_thm = Q.prove (
  `!m. m ≠ Tip ⇒ deletefindmin_1_side m`,
  ho_match_mp_tac balanced_mapTheory.deleteFindMin_ind >>
  ONCE_REWRITE_TAC [theorem "deletefindmin_1_side_def"] >>
  rw [] >>
  ONCE_REWRITE_TAC [theorem "deletefindmin_1_side_def"] >>
  rw [] >>
  metis_tac []) |> update_precondition;

val _ = translate balanced_mapTheory.glue_def;

val glue_side_thm = Q.prove (
  `!m n. glue_1_side m n`,
  rw [fetch "-" "glue_1_side_def"] >>
  metis_tac [deleteFindmin_side_thm, deleteFindmax_side_thm,
    balanced_mapTheory.balanced_map_distinct])
  |> update_precondition;

val _ = translate balanced_mapTheory.trim_help_greater_def;
val _ = translate balanced_mapTheory.trim_help_lesser_def;
val _ = translate balanced_mapTheory.trim_help_middle_def;
val _ = translate balanced_mapTheory.trim_def;
val _ = translate balanced_mapTheory.insertMin_def;
val _ = translate balanced_mapTheory.insertMax_def;
val _ = translate balanced_mapTheory.bin_def;
val _ = translate balanced_mapTheory.link_def;
val _ = translate balanced_mapTheory.filterLt_help_def;
val _ = translate balanced_mapTheory.filterLt_def;
val _ = translate balanced_mapTheory.filterGt_help_def;
val _ = translate balanced_mapTheory.filterGt_def;
val _ = translate balanced_mapTheory.insertR_def;
val _ = translate balanced_mapTheory.hedgeUnion_def;
val _ = translate balanced_mapTheory.splitLookup_def;
val _ = translate balanced_mapTheory.submap'_def;

val _ = translate balanced_mapTheory.null_def;
val _ = translate balanced_mapTheory.lookup_def;
val _ = translate balanced_mapTheory.member_def;
val _ = translate balanced_mapTheory.empty_def;
val _ = translate balanced_mapTheory.insert_def;
val _ = translate balanced_mapTheory.delete_def;
val _ = translate balanced_mapTheory.union_def;
val _ = translate balanced_mapTheory.foldrWithKey_def;
val _ = translate balanced_mapTheory.toAscList_def;
val _ = translate balanced_mapTheory.compare_def;
val _ = translate balanced_mapTheory.map_def;
val _ = translate balanced_mapTheory.isSubmapOfBy_def;
val _ = translate balanced_mapTheory.isSubmapOf_def;
val _ = translate balanced_mapTheory.fromList_def;

(* -- end of translation of balanced_map -- *)

val r = translate regexp_compareW_def;

val _ = add_preferred_thy "-";
val r = save_thm("mergesortN_ind", mergesortTheory.mergesortN_ind |> REWRITE_RULE[GSYM mllistTheory.drop_def]);
val r = translate (mergesortTheory.mergesortN_def |> REWRITE_RULE[GSYM mllistTheory.drop_def]);

val _ = use_mem_intro := true;
val r = translate build_or_def;
val _ = use_mem_intro := false;

val r = translate normalize_def;

val r = translate mem_regexp_def;
val r = translate exec_dfa_def;

val r = translate Brz_def;

(* Version of compile_regexp that avoids dom_Brz and Brzozo.
   The latter functions are probably untranslatable. *)
val compile_regexp_with_limit_def =
 Define
   `compile_regexp_with_limit r =
      let r' = normalize r in
      case Brz balanced_map$empty [r']
               (1n, balanced_map$singleton r' 0n, []) MAXNUM_32 of
          NONE => NONE
        | SOME(states,last_state,state_numbering,table) =>
      (let delta_vecs = table_to_vectors table in
      let accepts_vec = accepts_to_vector (get_accepts state_numbering) last_state
      in
         SOME(state_numbering,
          delta_vecs,
          accepts_vec))`;

Theorem Brz_sound_wrt_Brzozo:
   Brz seen worklist acc d = SOME result ==> Brzozo seen worklist acc = result
Proof
  rpt strip_tac
  >> `IS_SOME (Brz seen worklist acc d)`
       by rw[optionTheory.IS_SOME_DEF]
  >> `IS_SOME (Brz seen worklist acc (rdepth seen worklist acc))`
       by (rw[optionTheory.IS_SOME_DEF] >> metis_tac [rdepth_thm])
  >> `Brz seen worklist acc d = Brz seen worklist acc (rdepth seen worklist acc)`
       by metis_tac [Brz_determ]
  >> fs[Brzozo_def]
QED

Theorem Brz_sound_wrt_Brzozowski:
   Brz seen worklist acc d = SOME result ==> Brzozowski seen worklist acc = result
Proof
  rpt strip_tac
  >> `IS_SOME (Brz seen worklist acc d)`
       by rw[optionTheory.IS_SOME_DEF]
  >> rw[Brzozowski_def,dom_Brz_def]
  >> metis_tac[Brz_sound_wrt_Brzozo]
QED

Theorem compile_regexp_with_limit_sound:
   compile_regexp_with_limit r = SOME result ==> compile_regexp r = result
Proof
  fs[compile_regexp_with_limit_def,compile_regexp_def]
  >> every_case_tac
  >> IMP_RES_TAC Brz_sound_wrt_Brzozowski
  >> rw[pairTheory.ELIM_UNCURRY]
QED

val r = translate compile_regexp_with_limit_def;

val regexp_matcher_with_limit_def =
 Define
  `regexp_matcher_with_limit r s =
    case compile_regexp_with_limit r of
           NONE => NONE
         | SOME (state_numbering,deltaL,accepts) =>
   (let start_state = THE (balanced_map$lookup regexp_compare
                               (normalize r) state_numbering) in
    let acceptsV = fromList accepts in
    let deltaV = fromList (MAP fromList deltaL)
    in
      SOME(exec_dfa acceptsV deltaV start_state s))`;

Theorem regexp_matcher_with_limit_sound:
   regexp_matcher_with_limit r s = SOME result ==> regexp_matcher r s = result
Proof
  fs[regexp_matcher_with_limit_def,regexp_matcher_def]
  >> every_case_tac
  >> IMP_RES_TAC compile_regexp_with_limit_sound
  >> rw[pairTheory.ELIM_UNCURRY]
QED

val r = translate (regexp_matcher_with_limit_def);

val mem_tolist = Q.prove(`MEM (toList l) (MAP toList ll) = MEM l ll`,
  Induct_on `ll` >> fs[]);

val EL_map_toList = Q.prove(`!n. n < LENGTH l ==> EL n' (EL n (MAP toList l)) = sub (EL n l) n'`,
  Induct_on `l`
  >> fs[]
  >> rpt strip_tac
  >> Cases_on `n`
  >> fs[mlvectorTheory.EL_toList]);

val length_tolist_cancel = Q.prove(
  `!n. n < LENGTH l ==> LENGTH (EL n (MAP mlvector$toList l)) = length (EL n l)`,
  Induct_on `l`
  >> fs[]
  >> rpt strip_tac
  >> Cases_on `n`
  >> fs[mlvectorTheory.length_toList]);

val exec_dfa_side_imp = Q.prove(
  `!finals table n s.
   good_vec (MAP toList (toList table)) (toList finals)
    /\ EVERY (λc. MEM (ORD c) ALPHABET) (EXPLODE s)
    /\ n < length finals
   ==> exec_dfa_side finals table n s`,
  Induct_on `s`
  >- fs[fetch "-" "exec_dfa_side_def"]
  >> PURE_ONCE_REWRITE_TAC [fetch "-" "exec_dfa_side_def"]
  >> fs[good_vec_def,mlvectorTheory.length_toList]
  >> rpt GEN_TAC
  >> Induct_on `table`
   >> rpt strip_tac
   >> fs[sub_def,length_def,mlvectorTheory.toList_thm]
   >> `MEM (toList (EL n l)) (MAP toList l)`
        by fs[EL_MEM,mem_tolist,mlvectorTheory.toList_thm]
   >- metis_tac[mlvectorTheory.length_toList]
   >> first_x_assum(MATCH_MP_TAC o Q.SPECL [`finals`,`Vector l`, `x1`])
    >> rpt strip_tac
    >> fs[mlvectorTheory.toList_thm, length_def, mem_tolist]
    >- metis_tac[]
    >> first_x_assum(ASSUME_TAC o Q.SPECL [`toList (EL n l)`,`ORD h`])
    >> first_x_assum(MATCH_MP_TAC o Q.SPECL [`n`,`ORD h`,`x1`])
    >> rfs[mlvectorTheory.length_toList,mem_tolist,EL_map_toList,length_tolist_cancel]);

val compile_regexp_with_limit_dom_brz = Q.prove(
  `!r result.
    compile_regexp_with_limit r = SOME result
    ==> dom_Brz empty [normalize r] (1,singleton (normalize r) 0, [])`,
  rw[compile_regexp_with_limit_def, dom_Brz_def, MAXNUM_32_def]
  >> every_case_tac
  >> metis_tac [IS_SOME_EXISTS]);

val compile_regexp_with_limit_lookup = Q.prove(
  `!r state_numbering delta accepts.
   compile_regexp_with_limit r = SOME(state_numbering,delta,accepts)
   ==> IS_SOME(lookup regexp_compare (normalize r) state_numbering)`,
  rpt strip_tac
  >> `normalize r ∈ fdom regexp_compare state_numbering`
       by(metis_tac[compile_regexp_with_limit_dom_brz,
                    compile_regexp_good_vec,
                    compile_regexp_with_limit_sound])
  >> fs[eq_cmp_bmapTheory.fdom_def]);

Theorem tolist_fromlist_map_cancel:
   MAP mlvector$toList (MAP fromList ll) = ll
Proof
  Induct_on `ll` >> fs[]
QED

val regexp_matcher_with_limit_side_def = Q.prove(
  `!r s. regexp_matcher_with_limit_side r s ⇔ T`,
  rw[fetch "-" "regexp_matcher_with_limit_side_def"]
  >> rpt strip_tac
  >- (match_mp_tac exec_dfa_side_imp
      >> rpt strip_tac
      >- (rw[tolist_fromlist_map_cancel]
       >> metis_tac[compile_regexp_with_limit_dom_brz,
                    compile_regexp_good_vec,
                    compile_regexp_with_limit_sound])
      >- simp_tac list_ss [mem_alphabet_iff,ORD_BOUND,alphabet_size_def]
      >- (first_assum(ASSUME_TAC o MATCH_MP compile_regexp_with_limit_lookup)
          >> fs[IS_SOME_EXISTS,length_def,fromList_def]
          >> first_assum(fn thm =>
                         ASSUME_TAC(CONJ (MATCH_MP compile_regexp_with_limit_dom_brz thm)
                                         (MATCH_MP compile_regexp_with_limit_sound thm)))
          >> first_assum (ASSUME_TAC o MATCH_MP compile_regexp_good_vec)
          >> fs[good_vec_def] >> metis_tac []))
  >- metis_tac [compile_regexp_with_limit_lookup]) |> update_precondition;

(* TODO: should this be in regexp_compilerTheory *)

Theorem regexp_matcher_correct:
   dom_Brz_alt empty [normalize r] ⇒
   (regexp_matcher r s ⇔ s ∈ regexp_lang r)
Proof
  rw[regexp_matcher_def]
  \\ pairarg_tac \\ fs[]
  \\ imp_res_tac compile_regexp_good_vec
  \\ rfs[dom_Brz_alt_equal,eq_cmp_bmapTheory.fdom_def]
  \\ imp_res_tac Brzozowski_partial_eval_256
  \\ simp[IN_DEF]
QED

(* -- *)

(* TODO: translate PEG machinery as separate module?
         n.b. INTRO_FLOOKUP is copied from parserProgScript.sml
*)

Theorem INTRO_FLOOKUP:
   (if n IN FDOM G.rules
     then EV (G.rules ' n) i r y fk
     else Result xx) =
    (case FLOOKUP G.rules n of
       NONE => Result xx
     | SOME x => EV x i r y fk)
Proof
  SRW_TAC [] [finite_mapTheory.FLOOKUP_DEF]
QED

val coreloop_def' =
( pegexecTheory.coreloop_def
    |> REWRITE_RULE [INTRO_FLOOKUP]
    |> SPEC_ALL |> ONCE_REWRITE_RULE [FUN_EQ_THM]);

val r = translate coreloop_def';

val r = translate (pegexecTheory.peg_exec_def);

(* -- *)

val all_charsets_def = Define `
  all_charsets = Vector (GENLIST (\n. charset_sing (CHR n)) 256)`;

val all_charsets_eq = EVAL ``all_charsets``;

val charset_sing_eq = prove(
  ``!c. charset_sing c = sub all_charsets (ORD c)``,
  Cases
  \\ `ORD (CHR n) = n` by fs [ORD_CHR]
  \\ asm_rewrite_tac [sub_def,all_charsets_def]
  \\ fs [EL_GENLIST]);

val r = translate all_charsets_eq;
val r = translate charset_sing_eq;

val charset_sing_side = prove(
  ``!c. charset_sing_side c = T``,
  fs [fetch "-" "charset_sing_side_def"] \\ rw []
  \\ match_mp_tac LESS_LESS_EQ_TRANS
  \\ qexists_tac `256` \\ fs [ORD_BOUND] \\ EVAL_TAC)
  |> update_precondition

val _ = use_mem_intro := true;
val r = translate EscapableChar_def;
val _ = use_mem_intro := false;

val r = translate uncharset_char_def
val uncharset_char_side = Q.prove(
  `!x. uncharset_char_side x = T`,
    rw[definition"uncharset_char_side_def"]
    \\ once_rewrite_tac[WORD_AND_COMM]
    \\ `255n = 2 ** 8 - 1` by simp[] \\ pop_assum SUBST1_TAC
    \\ rename1`w  && _` \\ Cases_on`w`
    \\ simp[WORD_AND_EXP_SUB1]
    \\ `n MOD 256 < 256` by simp[]
    \\ simp[]) |> update_precondition;

val r = translate rePEG_def;

val r = translate parse_regexp_def;

val termination_lemma =
  MATCH_MP pegexecTheory.coreloop_total wfG_rePEG
  |> SIMP_RULE(srw_ss())[coreloop_def']

val parse_regexp_side = Q.prove(
  `∀x. parse_regexp_side x = T`,
  rw[definition"parse_regexp_side_def"] \\
  rw[definition"peg_exec_side_def"] \\
  rw[definition"coreloop_side_def"] \\
  qspec_then`MAP add_loc x`strip_assume_tac (Q.GEN`i`termination_lemma) \\
  qmatch_abbrev_tac`IS_SOME (OWHILE f g h)` \\
  qmatch_assum_abbrev_tac`OWHILE f g' h = SOME _` \\
  `g' = g` by (
    unabbrev_all_tac
    \\ simp[FUN_EQ_THM]
    \\ Cases \\ simp[]
    \\ TOP_CASE_TAC \\ simp[] ) \\ fs[]) |> update_precondition;

(* -- *)

val print_matching_lines = process_topdecs`
  fun print_matching_lines match prefix fd =
    case TextIO.inputLine fd of None => ()
    | Some ln => (if match ln then (TextIO.print prefix; TextIO.print ln) else ();
                  print_matching_lines match prefix fd)`;
val _ = append_prog print_matching_lines;

Theorem print_matching_lines_spec:
   (STRING_TYPE --> BOOL) m mv ∧ STRING_TYPE pfx pfxv ∧
   INSTREAM fd fdv ∧ fd ≠ 1 ∧ fd ≠ 2 ∧
   IS_SOME (get_file_content fs fd) ∧ get_mode fs fd = SOME ReadMode ⇒
   app (p:'ffi ffi_proj)
     ^(fetch_v "print_matching_lines"(get_ml_prog_state())) [mv; pfxv; fdv]
     (STDIO fs)
     (POSTv uv.
       &UNIT_TYPE () uv *
       STDIO (add_stdout (fastForwardFD fs fd)
                     (concat
                        (MAP (strcat pfx)
                           (FILTER m (MAP implode (linesFD fs fd)))))))
Proof
  Induct_on`linesFD fs fd` \\ rw[]
  >- (
    qpat_x_assum`[] = _`(assume_tac o SYM) \\ fs[]
    \\ xcf"print_matching_lines"(get_ml_prog_state())
    \\ xlet_auto >- xsimpl
    \\ rfs[linesFD_nil_lineFD_NONE,OPTION_TYPE_def]
    \\ xmatch
    \\ xcon
    \\ fs[lineFD_NONE_lineForwardFD_fastForwardFD]
    \\ reverse(Cases_on`STD_streams (fastForwardFD fs fd)`) >- (fs[STDIO_def] \\ xsimpl)
    \\ imp_res_tac STD_streams_stdout
    \\ imp_res_tac add_stdo_nil
    \\ xsimpl )
  \\ reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull)
  \\ qpat_x_assum`_::_ = _`(assume_tac o SYM) \\ fs[]
  \\ xcf"print_matching_lines"(get_ml_prog_state())
  \\ xlet_auto >- xsimpl
  \\ Cases_on`lineFD fs fd` \\ fs[GSYM linesFD_nil_lineFD_NONE]
  \\ fs[OPTION_TYPE_def]
  \\ xmatch
  \\ rename1`lineFD _ _ = SOME ln`
  \\ rveq
  \\ xlet_auto >- xsimpl
  (* TODO: xlet_auto doesn't handle if statements yet *)
  \\ xlet`POSTv x. STDIO (add_stdout (lineForwardFD fs fd)
                                     (if m (implode ln) then strcat pfx (implode ln) else strlit""))`
  >- (
    xif
    >- (
      (* TODO: xlet_auto failing on STDIO *)
      xlet`POSTv x. STDIO (add_stdout (lineForwardFD fs fd) pfx)`
      >- (xapp \\ instantiate \\ xsimpl
          \\ CONV_TAC(SWAP_EXISTS_CONV) \\ qexists_tac`lineForwardFD fs fd`
          \\ xsimpl )
      \\ xapp \\ instantiate \\ xsimpl
      (* TODO: make this less painful? *)
      \\ CONV_TAC(SWAP_EXISTS_CONV) \\ qexists_tac`add_stdout (lineForwardFD fs fd) pfx`
      \\ xsimpl \\ rw[]
      (* TODO: make this less painful? *)
      \\ imp_res_tac STD_streams_lineForwardFD
      \\ imp_res_tac STD_streams_stdout
      \\ imp_res_tac add_stdo_o
      \\ xsimpl)
    \\ xcon
    \\ DEP_REWRITE_TAC[GEN_ALL add_stdo_nil]
    \\ xsimpl
    \\ metis_tac[STD_streams_stdout,STD_streams_lineForwardFD])
  \\ imp_res_tac linesFD_cons_imp \\ rveq \\ fs[]
  \\ qmatch_goalsub_abbrev_tac`STDIO fs'`
  \\ first_x_assum(qspecl_then[`fs'`,`fd`]mp_tac)
  \\ simp[AND_IMP_INTRO]
  \\ impl_keep_tac
  >- (
    simp[Abbr`fs'`]
    \\ qmatch_goalsub_rename_tac`add_stdout _ x`
    \\ DEP_REWRITE_TAC[linesFD_add_stdout]
    \\ simp[STD_streams_lineForwardFD,get_file_content_add_stdout] )
  \\ strip_tac
  \\ xapp
  \\ xsimpl
  \\ qmatch_goalsub_abbrev_tac`STDIO fs1 ==>> STDIO fs2 * _`
  \\ `fs1 = fs2` suffices_by xsimpl
  \\ fs[Abbr`fs1`,Abbr`fs2`]
  \\ qpat_x_assum`_ = linesFD fs' fd`(assume_tac o SYM) \\ fs[]
  \\ simp[Abbr`fs'`,linesFD_add_stdout]
  \\ simp[add_stdout_lineForwardFD]
  \\ simp[add_stdout_fastForwardFD,STD_streams_fastForwardFD]
  \\ DEP_REWRITE_TAC[add_stdout_fastForwardFD]
  \\ simp[STD_streams_add_stdout]
  \\ DEP_REWRITE_TAC[GEN_ALL add_stdo_o]
  \\ conj_tac >- metis_tac[STD_streams_stdout]
  \\ rw[concat_cons]
QED

val notfound_string_def = Define`
  notfound_string f = concat[strlit"cake_grep: ";f;strlit": No such file or directory\n"]`;

val r = translate notfound_string_def;

val print_matching_lines_in_file = process_topdecs`
  fun print_matching_lines_in_file m file =
    let val fd = TextIO.openIn file
    in (print_matching_lines m (String.concat[file,":"]) fd;
        TextIO.closeIn fd)
    end handle TextIO.BadFileName =>
        TextIO.output TextIO.stdErr (notfound_string file)`;
val _ = append_prog print_matching_lines_in_file;

Theorem print_matching_lines_in_file_spec:
   FILENAME f fv ∧ hasFreeFD fs ∧
   (STRING_TYPE --> BOOL) m mv
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"print_matching_lines_in_file"(get_ml_prog_state()))
     [mv; fv]
     (STDIO fs)
     (POSTv uv. &UNIT_TYPE () uv *
                STDIO (if inFS_fname fs f
                   then add_stdout fs
                      (concat
                          (MAP (strcat f o strcat (strlit":"))
                            (FILTER m (all_lines fs f))))
                   else add_stderr fs (notfound_string f)))
Proof
  xcf"print_matching_lines_in_file"(get_ml_prog_state())
  \\ reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull)
  \\ reverse(Cases_on`consistentFS fs`)
  >-(fs[STDIO_def,IOFS_def] >> xpull >> fs[wfFS_def,consistentFS_def] >> res_tac)
  \\ qmatch_goalsub_abbrev_tac`_ * STDIO fs'`
  \\ reverse(xhandle`POSTve
       (λv. &UNIT_TYPE () v * STDIO fs')
       (λe. &(BadFileName_exn e ∧ ¬inFS_fname fs f) * STDIO fs)`)
  >- (
    xcases
    \\ fs[BadFileName_exn_def]
    \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
    \\ xlet_auto >- xsimpl
    \\ xapp_spec output_stderr_spec \\ instantiate \\ xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`fs`
    \\ xsimpl)
  >- ( xsimpl )
  \\ xlet_auto_spec(SOME (SPEC_ALL openIn_STDIO_spec))
  >- ( xsimpl )
  >- ( xsimpl )
  \\ xlet_auto
  >- ( xcon \\ xsimpl \\ fs[ml_translatorTheory.LIST_TYPE_def] )
  \\ xlet_auto
  >- ( xcon \\ xsimpl \\ fs[ml_translatorTheory.LIST_TYPE_def] )
  \\ xlet_auto
  >- ( xcon \\ xsimpl \\ fs[ml_translatorTheory.LIST_TYPE_def,FILENAME_def] )
  \\ qmatch_assum_rename_tac`lv = Conv _ [fv;_]`
  \\ `LIST_TYPE STRING_TYPE [f;strlit":"] lv` by ( fs[LIST_TYPE_def,FILENAME_def] )
  \\ rveq
  \\ xlet_auto >- xsimpl
  \\ qmatch_asmsub_abbrev_tac`add_stdout fs out`
  \\ imp_res_tac nextFD_ltX
  \\ progress inFS_fname_ALOOKUP_EXISTS
  \\ progress IS_SOME_get_file_content_openFileFS_nextFD \\ rfs[]
  \\ imp_res_tac STD_streams_nextFD
  \\ rpt(first_x_assum(qspecl_then[`0`,`ReadMode`]strip_assume_tac))
  \\ xlet_auto >- (
    xsimpl
    \\ simp[get_mode_def]
    \\ DEP_REWRITE_TAC[ALOOKUP_inFS_fname_openFileFS_nextFD]
    \\ simp[] )
  \\ xapp_spec closeIn_STDIO_spec
  \\ instantiate
  \\ qmatch_goalsub_abbrev_tac`STDIO fs'' ==>> _`
  \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`fs''`
  \\ xsimpl
  \\ reverse(rw[Abbr`fs''`,Abbr`fs'`,Abbr`out`])
  >- (
    simp[validFileFD_def]
    \\ imp_res_tac ALOOKUP_inFS_fname_openFileFS_nextFD
    \\ rfs[] )
  \\ simp[o_DEF,mlstringTheory.concat_thm,mlstringTheory.strcat_thm]
  \\ fs[linesFD_openFileFS_nextFD]
  \\ srw_tac[ETA_ss][FILTER_MAP,o_DEF]
  \\ simp[MAP_MAP_o,o_DEF]
  \\ rewrite_tac[GSYM APPEND_ASSOC,GSYM CONS_APPEND]
  \\ simp[GSYM add_stdo_ADELKEY,openFileFS_ADELKEY_nextFD]
  \\ xsimpl
QED

val usage_string_def = Define`
  usage_string = strlit"Usage: grep <regex> <file> <file>...\n"`;

val r = translate usage_string_def;

val usage_string_v_thm = theorem"usage_string_v_thm";

val parse_failure_string_def = Define`
  parse_failure_string r = concat[strlit"Could not parse regexp: ";r;strlit"\n"]`;

val r = translate parse_failure_string_def;

(* TODO: This approach (with matcher argument as a function) does not play nicely with CF
val match_line_def = Define`
  match_line matcher (line:string) =
  case matcher line of | SOME T => T | _ => F`;

val r = translate match_line_def;
*)
val match_line_def = Define`
  match_line r s =
    case regexp_matcher_with_limit r s of | SOME T => T | _ => F`;

val r = translate match_line_def;

val build_matcher_def = Define`
  build_matcher r s =
    if strlen s = 0 then
      match_line r []
    else
      match_line r (FRONT (explode s))`;

val r = translate build_matcher_def;

val build_matcher_side = Q.prove(
  `∀r s. build_matcher_side r s = T`,
  rw[definition"build_matcher_side_def"]
  \\ Cases_on`s` \\ fs[LENGTH_NIL]) |> update_precondition;

val build_matcher_v_thm = theorem"build_matcher_v_thm"

Theorem build_matcher_partial_spec:
   REGEXP_REGEXP_TYPE r rv ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"build_matcher"(get_ml_prog_state())) [rv] emp
    (POSTv v. &(STRING_TYPE --> BOOL) (build_matcher r) v)
Proof
  strip_tac
  \\ rw[app_def]
  \\ irule Arrow_IMP_app_basic
  \\ instantiate
  \\ simp[build_matcher_v_thm]
QED

val grep = process_topdecs`
  fun grep u =
    case CommandLine.arguments ()
    of [] => TextIO.output TextIO.stdErr usage_string
     | [_] => TextIO.output TextIO.stdErr usage_string
     | (regexp::files) =>
       case parse_regexp (String.explode regexp) of
         None => TextIO.output TextIO.stdErr (parse_failure_string regexp)
       | Some r =>
           (* abandoning this approach for now ...
         let
           (* TODO: this would be nicer as:
           val raw_match = match_line (regexp_matcher_with_limit r)
             but how does partial application work in CF? *)
           val raw_match = (fn s => match_line (fn s => regexp_matcher_with_limit r s) s)
         in
           *)
           (* TODO: similar issue with higher-order function, CF seems to need this eta  *)
           List.app (fn file => print_matching_lines_in_file (build_matcher r) file) files
         (* end *)`;
val _ = append_prog grep;

(* TODO: maybe these would be better with the arguments flipped? *)
val _ = temp_overload_on("addout",``combin$C add_stdout``);
val _ = temp_overload_on("adderr",``combin$C add_stderr``);

val grep_sem_file_def = Define`
  grep_sem_file L filename fs =
    case ALOOKUP fs.files filename of
    | NONE => adderr (notfound_string filename) fs
    | SOME ino =>
        case ALOOKUP fs.inode_tbl (File ino) of
        | SOME contents =>
        addout
          (concat
            (MAP (λmatching_line. concat [filename;strlit":";implode matching_line;strlit"\n"])
               (FILTER (λline. line ∈ L) (splitlines contents)))) fs`;

val grep_sem_def = Define`
  (grep_sem (_::regexp::filenames) (fs : fsFFI$IO_fs) =
   if NULL filenames then adderr usage_string fs else
   case parse_regexp (explode regexp) of
   | NONE => adderr (parse_failure_string regexp) fs
   | SOME r =>
       FOLDL
         (λaction filename.
           grep_sem_file (regexp_lang r) filename
             o action)
         I filenames fs) ∧
  (grep_sem _ fs = adderr usage_string fs)`;

val grep_sem_ind = theorem"grep_sem_ind";

(*
  grep_sem_def
  |> CONV_RULE(RESORT_FORALL_CONV List.rev)
  |> Q.SPEC`[f1;f2;f3]`
  |> SIMP_RULE(srw_ss())[]
*)

Theorem grep_sem_file_MAP_FST_infds[simp]:
   consistentFS fs ⇒ MAP FST (grep_sem_file L nm fs).infds = MAP FST fs.infds
Proof
  rw[grep_sem_file_def] \\ CASE_TAC \\ simp[] \\ CASE_TAC \\ simp[]
  \\ fs[consistentFS_def] \\ res_tac \\ fs[ALOOKUP_NONE]
QED

Theorem grep_sem_file_maxFD[simp]:
   consistentFS fs ⇒ (grep_sem_file L nm fs).maxFD = fs.maxFD
Proof
  rw[grep_sem_file_def,consistentFS_def] \\ CASE_TAC \\ simp[] \\ res_tac \\
  CASE_TAC \\ fs[ALOOKUP_NONE]
QED

Theorem STD_streams_grep_sem_file:
   consistentFS fs /\ STD_streams fs ⇒ STD_streams (grep_sem_file L fn fs)
Proof
  rw[grep_sem_file_def,consistentFS_def]
  \\ rpt CASE_TAC \\ simp[STD_streams_add_stderr,STD_streams_add_stdout]
  \\ res_tac >> fs[ALOOKUP_NONE]
QED

Theorem consistentFS_grep_sem_file[simp]:
   consistentFS fs ⇒
    consistentFS (grep_sem_file L fn fs)
Proof
 rw[grep_sem_file_def,consistentFS_def]
  \\ rpt CASE_TAC
  \\ fs[up_stdo_files,add_stdo_def] \\
  res_tac >> fs[ALOOKUP_NONE]
QED

Theorem grep_sem_file_lemma:
   consistentFS fs /\ STD_streams fs ⇒
   let fs' = FOLDL (λa f. grep_sem_file L f o a) I ls fs in
     STD_streams fs'∧ consistentFS fs' ∧ (hasFreeFD fs ⇒ hasFreeFD fs') ∧
     FILTER (isFile o FST) fs'.inode_tbl = FILTER (isFile o FST) fs.inode_tbl ∧
     fs'.files = fs.files
Proof
  simp[]
  \\ qid_spec_tac`fs`
  \\ qid_spec_tac`ls`
  \\ ho_match_mp_tac SNOC_INDUCT
  \\ rw[FOLDL_SNOC,STD_streams_grep_sem_file,consistentFS_grep_sem_file,FOLDL_APPEND]
  \\ rw[Once grep_sem_file_def]
  >-(NTAC 2 (CASE_TAC \\
       simp[FILTER_File_add_stderr,FILTER_File_add_stdout])
     \\ res_tac \\ fs[consistentFS_def] \\ res_tac \\ fs[ALOOKUP_NONE])
  >-(rpt (CASE_TAC \\
       simp[FILTER_File_add_stderr,FILTER_File_add_stdout,add_stdo_def,up_stdo_def,fsupdate_def])
     \\ res_tac \\ fs[consistentFS_def] \\ res_tac \\ fs[ALOOKUP_NONE])
QED

Theorem grep_sem_file_lemma':
   consistentFS fs ⇒
     consistentFS (FOLDL (λa f. grep_sem_file L f o a) I ls fs)
Proof
 simp[]
  \\ qid_spec_tac`fs`
  \\ qid_spec_tac`ls`
  \\ ho_match_mp_tac SNOC_INDUCT
  \\ rw[FOLDL_SNOC,consistentFS_grep_sem_file,FOLDL_APPEND]
QED

Theorem grep_sem_file_with_numchars:
   consistentFS fs ⇒
   grep_sem_file L filename (fs with numchars := ns) =
   grep_sem_file L filename fs with numchars := ns
Proof
  rw[grep_sem_file_def,consistentFS_def] \\ CASE_TAC \\ rw[add_stdo_with_numchars]
  \\ CASE_TAC \\ res_tac \\ fs[ALOOKUP_NONE]
QED

Theorem grep_sem_with_numchars:
   ∀cl fs. consistentFS fs ⇒
   grep_sem cl (fs with numchars := ns) =
   grep_sem cl fs with numchars := ns
Proof
  recInduct grep_sem_ind
  \\ rw[grep_sem_def,add_stdo_with_numchars]
  \\ CASE_TAC \\ rw[add_stdo_with_numchars]
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ pop_assum kall_tac
  \\ qid_spec_tac`fs`
  \\ qid_spec_tac`filenames`
  \\ ho_match_mp_tac SNOC_INDUCT
  \\ rw[FOLDL_SNOC,FOLDL_APPEND]
  \\ rw[grep_sem_file_with_numchars,grep_sem_file_lemma']
QED

val grep_termination_assum_def = Define`
  (grep_termination_assum (_::regexp::filenames) ⇔
   if NULL filenames then T else
     case parse_regexp (explode regexp) of
     | NONE => T
     | SOME r => IS_SOME (Brz empty [normalize r] (1,singleton (normalize r) 0,[]) MAXNUM_32)) ∧
  (grep_termination_assum _ ⇔ T)`;

Theorem grep_spec:
   hasFreeFD fs ∧
   grep_termination_assum cl
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"grep"(get_ml_prog_state()))
    [Conv NONE []]
    (STDIO fs * COMMANDLINE cl)
    (POSTv v. &UNIT_TYPE () v * STDIO (grep_sem cl fs) * COMMANDLINE cl)
Proof
  strip_tac
  \\ xcf"grep"(get_ml_prog_state())
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ reverse(Cases_on`wfcl cl`)>-(fs[COMMANDLINE_def] \\ xpull)
  \\ reverse(Cases_on`consistentFS fs`)
  >-(fs[STDIO_def,IOFS_def,wfFS_def,consistentFS_def] >> xpull >> res_tac)
  \\ xlet_auto >- xsimpl
  \\ Cases_on`cl` \\ fs[wfcl_def]
  \\ Cases_on`t` \\ fs[LIST_TYPE_def]
  >- (
    xmatch
    \\ xapp_spec output_stderr_spec
    \\ simp[grep_sem_def]
    \\ xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`usage_string`
    \\ simp[usage_string_v_thm]
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`fs`
    \\ xsimpl
    )
  \\ rveq
  \\ rename1`EVERY validArg t`
  \\ Cases_on`t` \\ fs[LIST_TYPE_def]
  >- (
    xmatch
    \\ xapp_spec output_stderr_spec
    \\ simp[grep_sem_def]
    \\ xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`usage_string`
    \\ simp[usage_string_v_thm]
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`fs`
    \\ xsimpl )
  \\ rveq
  \\ xmatch
  \\ rename1`grep_sem (grep::regexp::file1::files)`
  \\ simp[grep_sem_def]
  \\ qmatch_goalsub_abbrev_tac`COMMANDLINE cl`
  \\ qmatch_assum_abbrev_tac`Abbrev(cl = grep::regexp::fls)`
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ Cases_on`parse_regexp (explode regexp)` \\ fs[OPTION_TYPE_def]
  >- (
    xmatch
    \\ xlet_auto >- xsimpl
    \\ xapp_spec output_stderr_spec
    \\ instantiate
    \\ xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`fs`
    \\ xsimpl)
  \\ qmatch_goalsub_abbrev_tac`FOLDL ff a0 files fs`
  \\ `FOLDL ff a0 files fs = FOLDL ff I fls fs` by simp[Abbr`fls`,Abbr`ff`]
  \\ pop_assum SUBST1_TAC
  \\ simp[Abbr`a0`]
  \\ xmatch
  \\ rename1`parse_regexp _ = SOME r`
  \\ qabbrev_tac`fcs = fs.inode_tbl`
  \\ xfun_spec`appthis`
     `∀f fv fs'.
      FILENAME f fv ∧ hasFreeFD fs' ∧ consistentFS fs' ∧
      FILTER (isFile o FST) fs'.inode_tbl = FILTER (isFile o FST) fs.inode_tbl ∧
      fs'.files = fs.files ⇒
      app p appthis [fv] (STDIO fs')
        (POSTv v. &UNIT_TYPE () v
                  * STDIO (grep_sem_file (regexp_lang r) f fs'))`
  >- (
    rw[]
    \\ first_x_assum match_mp_tac
    \\ xlet_auto >- xsimpl
    \\ xapp
    \\ instantiate
    \\ xsimpl
    \\ simp[grep_sem_file_def]
    \\ `ALOOKUP fs.inode_tbl (File f) = ALOOKUP fs'.inode_tbl (File f)`
    by (
      last_x_assum(mp_tac o Q.AP_TERM`ALOOKUP`)
      \\ disch_then(mp_tac o C Q.AP_THM`File f`)
      \\ simp[ALOOKUP_FILTER,o_DEF,LAMBDA_PROD] )
    \\ fs[]
    \\ reverse IF_CASES_TAC
    >- ( CASE_TAC \\ xsimpl \\ imp_res_tac ALOOKUP_SOME_inFS_fname \\
         fs[inFS_fname_def] >> rfs[])
    \\ CASE_TAC >-(fs[inFS_fname_def] \\ rfs[])
    \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS
    \\ rfs[]
    \\ qmatch_goalsub_abbrev_tac`add_stdout _ s1`
    \\ qmatch_goalsub_abbrev_tac`_ (add_stdout _ s2) * _`
    \\ `s1 = s2` suffices_by xsimpl
    \\ simp[Abbr`s1`,Abbr`s2`]
    \\ AP_TERM_TAC
    \\ simp[FILTER_MAP,concat_cons,MAP_MAP_o,o_DEF,
            all_lines_def,lines_of_def,implode_def]
    \\ AP_TERM_TAC
    \\ simp[FILTER_EQ,build_matcher_def,FRONT_APPEND]
    \\ gen_tac
    \\ fs[Abbr`cl`,grep_termination_assum_def,Abbr`fls`]
    \\ `dom_Brz_alt empty [normalize r]`
    by ( metis_tac[dom_Brz_alt_equal,dom_Brz_def] )
    \\ drule (GSYM(GEN_ALL regexp_matcher_correct)) \\ rw[]
    \\ rw[match_line_def]
    \\ TOP_CASE_TAC
    >- (
      fs[regexp_matcher_with_limit_def,compile_regexp_with_limit_def]
      \\ rfs[IS_SOME_EXISTS] \\ rfs[]
      \\ every_case_tac \\ fs[] )
    \\ imp_res_tac regexp_matcher_with_limit_sound
    \\ rveq \\ fs[])
  \\ reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull)
  \\ reverse(Cases_on`consistentFS fs`)
  >-(fs[STDIO_def,IOFS_def] >> xpull >> fs[wfFS_def,consistentFS_def] >> res_tac)
  \\ xapp_spec (INST_TYPE[alpha|->``:mlstring``]app_spec)
  \\ CONV_TAC (RESORT_EXISTS_CONV List.rev)
  \\ qexists_tac`λn. STDIO (FOLDL ff I (TAKE n fls) fs)`
  \\ xsimpl
  \\ qexists_tac`fls`
  \\ xsimpl
  \\ qexists_tac`STRING_TYPE`
  \\ reverse conj_tac
  >- ( simp[Abbr`fls`,LIST_TYPE_def] )
  \\ rw[] \\ rfs[EL_MAP]
  \\ qmatch_assum_abbrev_tac`STRING_TYPE f xv`
  \\ `validArg f`
  by (
    fs[Abbr`fls`,Abbr`f`,explode_implode,EVERY_MEM,MEM_EL,PULL_EXISTS]
    \\ Cases_on`n` \\ fs[] )
  \\ `FILENAME f xv`
  by (
    fs[FILENAME_def,validArg_def,Abbr`f`,explode_implode,implode_def]
    \\ fs[EVERY_MEM] )
  \\ first_x_assum drule
  \\ `TAKE (n+1) fls = (TAKE n fls) ++ [EL n fls]` by ( simp[TAKE_EL_SNOC] )
  \\ simp[FOLDL_APPEND,Abbr`ff`]
  \\ disch_then match_mp_tac
  \\ imp_res_tac grep_sem_file_lemma
  \\ fs[]
QED

val st = get_ml_prog_state()

Theorem grep_whole_prog_spec:
   consistentFS fs ⇒
   whole_prog_spec ^(fetch_v "grep" st) cl fs NONE
     ((=) (grep_sem cl fs))
Proof
  disch_then assume_tac
  \\ simp[whole_prog_spec_def]
  \\ qexists_tac`grep_sem cl fs`
  \\ simp[GSYM grep_sem_with_numchars,with_same_numchars]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe (UNDISCH grep_spec)))
  \\ xsimpl
QED

val name = "grep"
val spec = grep_whole_prog_spec |> UNDISCH
val (sem_thm,prog_tm) = whole_prog_thm st name spec

val grep_prog_def = Define`grep_prog = ^prog_tm`;

val grep_semantics = save_thm("grep_semantics",
  sem_thm |> REWRITE_RULE[GSYM grep_prog_def]
  |> DISCH_ALL |> SIMP_RULE(srw_ss())[AND_IMP_INTRO,GSYM CONJ_ASSOC]);

val _ = export_theory ();
