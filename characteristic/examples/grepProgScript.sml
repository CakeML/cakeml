open preamble ml_translatorLib ml_progLib
     cfTacticsLib basisFunctionsLib
     rofsFFITheory mlfileioProgTheory ioProgTheory
     charsetTheory regexpTheory regexp_parserTheory regexp_compilerTheory

val _ = new_theory "grepProg";

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

(* TODO: this is largely copied from the bootstrap translation
         can it be properly abstracted out? *)
local
  val ths = ml_translatorLib.eq_lemmas();
in
  fun find_equality_type_thm tm =
    first (can (C match_term tm) o rand o snd o strip_imp o concl) ths
end

val EqualityType_WORD = find_equality_type_thm``WORD``
val EqualityType_CHARSET_CHARSET_TYPE = find_equality_type_thm``CHARSET_CHARSET_TYPE``
  |> REWRITE_RULE[EqualityType_WORD]

val REGEXP_REGEXP_TYPE_def = theorem"REGEXP_REGEXP_TYPE_def";
val REGEXP_REGEXP_TYPE_ind = theorem"REGEXP_REGEXP_TYPE_ind";
val no_closures_def = ml_translatorTheory.no_closures_def;
val LIST_TYPE_def = ml_translatorTheory.LIST_TYPE_def;
val EqualityType_def = ml_translatorTheory.EqualityType_def;
val types_match_def = ml_translatorTheory.types_match_def;
val ctor_same_type_def = semanticPrimitivesTheory.ctor_same_type_def;

val REGEXP_REGEXP_TYPE_no_closures = Q.prove(
  `∀a b. REGEXP_REGEXP_TYPE a b ⇒ no_closures b`,
  ho_match_mp_tac REGEXP_REGEXP_TYPE_ind
  \\ rw[REGEXP_REGEXP_TYPE_def]
  \\ rw[no_closures_def]
  \\ TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y1`,`x1`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS,no_closures_def] >>
    qx_gen_tac`p` >>
    simp[PULL_EXISTS,no_closures_def] >>
    rw[] >>
    METIS_TAC[EqualityType_def] ) >>
  metis_tac[EqualityType_CHARSET_CHARSET_TYPE,
            EqualityType_def]);

val REGEXP_REGEXP_TYPE_types_match = Q.prove(
  `∀a b c d. REGEXP_REGEXP_TYPE a b ∧ REGEXP_REGEXP_TYPE c d ⇒ types_match b d`,
  ho_match_mp_tac REGEXP_REGEXP_TYPE_ind \\
  rw[REGEXP_REGEXP_TYPE_def] \\
  Cases_on`c` \\ fs[REGEXP_REGEXP_TYPE_def,types_match_def,ctor_same_type_def] \\ rw[] \\
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x2 y2` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y2`,`x2`,`y1`,`x1`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] >- (
      Cases >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] ) >>
    qx_gen_tac`p` >>
    gen_tac >> Cases >> simp[PULL_EXISTS,LIST_TYPE_def] >>
    rw[types_match_def,ctor_same_type_def] >>
    PROVE_TAC[EqualityType_def] ) >>
  metis_tac[EqualityType_CHARSET_CHARSET_TYPE,
            EqualityType_def]);

val REGEXP_REGEXP_TYPE_11 = Q.prove(
  `∀a b c d. REGEXP_REGEXP_TYPE a b ∧ REGEXP_REGEXP_TYPE c d ⇒ (a = c ⇔ b = d)`,
  ho_match_mp_tac REGEXP_REGEXP_TYPE_ind \\
  rw[REGEXP_REGEXP_TYPE_def] \\
  Cases_on`c` \\ fs[REGEXP_REGEXP_TYPE_def] \\ rw[EQ_IMP_THM] \\
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x y2` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y2`,`y1`,`x`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >>
    rw[] >>
    metis_tac[]) >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x2 y` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y`,`x1`,`x2`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >- (
      Cases \\ rw[LIST_TYPE_def] ) \\
    gen_tac \\ Cases \\ rw[LIST_TYPE_def] >>
    metis_tac[]) >>
  metis_tac[EqualityType_CHARSET_CHARSET_TYPE,
            EqualityType_def]);

val EqualityType_REGEXP_REGEXP_TYPE = Q.store_thm("EqualityType_REGEXP_REGEXP_TYPE",
  `EqualityType REGEXP_REGEXP_TYPE`,
  metis_tac[REGEXP_REGEXP_TYPE_no_closures,REGEXP_REGEXP_TYPE_types_match,REGEXP_REGEXP_TYPE_11,
  EqualityType_def]);

val _ = store_eq_thm EqualityType_REGEXP_REGEXP_TYPE;
(* -- *)

(* TODO: can the regexp one be avoided by using the mllist one instead? *)
val zip_eq_zip = Q.store_thm("zip_eq_zip",
  `regexp$zip = mllist$zip`,
  simp[FUN_EQ_THM]
  \\ ho_match_mp_tac mllistTheory.zip_ind
  \\ EVAL_TAC \\ rw[]);

val r = save_thm("regexp_compareW_ind", regexp_compareW_ind |> REWRITE_RULE[zip_eq_zip])
val _ = add_preferred_thy"-";
val r = translate (regexp_compareW_def |> REWRITE_RULE[zip_eq_zip]);

val r = save_thm("mergesortN_ind", mergesortTheory.mergesortN_ind |> REWRITE_RULE[GSYM mllistTheory.drop_def]);
val r = translate (mergesortTheory.mergesortN_def |> REWRITE_RULE[GSYM mllistTheory.drop_def]);

val _ = use_mem_intro := true;
val r = translate build_or_def;
val _ = use_mem_intro := false;

val r = translate (normalize_def);

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

val Brz_sound_wrt_Brzozo = Q.store_thm("Brz_sound_wrt_Brzozo",
  `Brz seen worklist acc d = SOME result ==> Brzozo seen worklist acc = result`,
  rpt strip_tac
  >> `IS_SOME (Brz seen worklist acc d)`
       by rw[optionTheory.IS_SOME_DEF]
  >> `IS_SOME (Brz seen worklist acc (rdepth seen worklist acc))`
       by (rw[optionTheory.IS_SOME_DEF] >> metis_tac [rdepth_thm])
  >> `Brz seen worklist acc d = Brz seen worklist acc (rdepth seen worklist acc)`
       by metis_tac [Brz_determ]
  >> fs[Brzozo_def]);

val Brz_sound_wrt_Brzozowski = Q.store_thm("Brz_sound_wrt_Brzozowski",
  `Brz seen worklist acc d = SOME result ==> Brzozowski seen worklist acc = result`,
  rpt strip_tac
  >> `IS_SOME (Brz seen worklist acc d)`
       by rw[optionTheory.IS_SOME_DEF]
  >> rw[Brzozowski_def,dom_Brz_def]
  >> metis_tac[Brz_sound_wrt_Brzozo]);

val compile_regexp_with_limit_sound = Q.store_thm("compile_regexp_with_limit_sound",
  `compile_regexp_with_limit r = SOME result ==> compile_regexp r = result`,
  fs[compile_regexp_with_limit_def,compile_regexp_def]
  >> every_case_tac
  >> IMP_RES_TAC Brz_sound_wrt_Brzozowski
  >> rw[pairTheory.ELIM_UNCURRY]);

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

val regexp_matcher_with_limit_sound = Q.store_thm("regexp_matcher_with_limit_sound",
  `regexp_matcher_with_limit r s = SOME result ==> regexp_matcher r s = result`,
  fs[regexp_matcher_with_limit_def,regexp_matcher_def]
  >> every_case_tac
  >> IMP_RES_TAC compile_regexp_with_limit_sound
  >> rw[pairTheory.ELIM_UNCURRY]);

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

val tolist_fromlist_map_cancel = Q.store_thm("tolist_fromlist_map_cancel",
  `MAP mlvector$toList (MAP fromList ll) = ll`,
  Induct_on `ll` >> fs[]);

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

val regexp_matcher_correct = Q.store_thm("regexp_matcher_correct",
  `dom_Brz_alt empty [normalize r] ⇒
   (regexp_matcher r s ⇔ s ∈ regexp_lang r)`,
  rw[regexp_matcher_def]
  \\ pairarg_tac \\ fs[]
  \\ imp_res_tac compile_regexp_good_vec
  \\ rfs[dom_Brz_alt_equal,eq_cmp_bmapTheory.fdom_def]
  \\ imp_res_tac Brzozowski_partial_eval_256
  \\ simp[IN_DEF]);

(* -- *)

(* TODO: translate PEG machinery as separate module?
         n.b. INTRO_FLOOKUP is copied from parserProgScript.sml
*)

val INTRO_FLOOKUP = Q.store_thm("INTRO_FLOOKUP",
  `(if n IN FDOM G.rules
     then EV (G.rules ' n) i r y fk
     else Result xx) =
    (case FLOOKUP G.rules n of
       NONE => Result xx
     | SOME x => EV x i r y fk)`,
  SRW_TAC [] [finite_mapTheory.FLOOKUP_DEF]);

val coreloop_def' =
( pegexecTheory.coreloop_def
    |> REWRITE_RULE [INTRO_FLOOKUP]
    |> SPEC_ALL |> ONCE_REWRITE_RULE [FUN_EQ_THM]);

val r = translate coreloop_def';

val r = translate (pegexecTheory.peg_exec_def);

(* -- *)

(* TODO: translate shifts as part of a separate module? word module? *)

val r = translate (shift_left_def |> spec64 |> CONV_RULE (wordsLib.WORD_CONV));

(* -- *)

val r = translate (charset_sing_def |> SIMP_RULE(srw_ss())[shift_left_rwt]);

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
    case FileIO.inputLine fd of NONE => ()
    | SOME ln => (if match ln then (print prefix; print ln) else ();
                  print_matching_lines match prefix fd)`;
val _ = append_prog print_matching_lines;

val print_matching_lines_spec = Q.store_thm("print_matching_lines_spec",
  `∀fs out.
   (STRING_TYPE --> BOOL) m mv ∧ STRING_TYPE pfx pfxv ∧
   WORD (fd:word8) fdv ∧ validFD (w2n fd) fs ⇒
   app (p:'ffi ffi_proj)
     ^(fetch_v "print_matching_lines"(get_ml_prog_state())) [mv; pfxv; fdv]
     (ROFS fs * STDOUT out)
     (POSTv uv.
       &UNIT_TYPE () uv *
       ROFS (bumpAllFD (w2n fd) fs) *
       STDOUT (out ++ CONCAT
         (MAP ((++) (explode pfx))
           (FILTER (m o implode)
             (MAP (combin$C (++) "\n")
               (linesFD (w2n fd) fs))))))`,
  Induct_on`linesFD (w2n fd) fs` \\ rw[]
  >- (
    qpat_x_assum`[] = _`(assume_tac o SYM) \\ fs[]
    \\ xcf"print_matching_lines"(get_ml_prog_state())
    \\ xlet`POSTv x. &OPTION_TYPE STRING_TYPE (OPTION_MAP implode (FDline (w2n fd) fs))  x *
                     ROFS (bumpLineFD (w2n fd) fs) * STDOUT out`
    >- ( xapp \\ instantiate \\ xsimpl )
    \\ rfs[GSYM FDline_NONE_linesFD,ml_translatorTheory.OPTION_TYPE_def]
    \\ xmatch
    \\ xcon
    \\ imp_res_tac FDline_NONE_bumpAll_bumpLine
    \\ xsimpl )
  \\ qpat_x_assum`_::_ = _`(assume_tac o SYM) \\ fs[]
  \\ xcf"print_matching_lines"(get_ml_prog_state())
  \\ xlet`POSTv x. &OPTION_TYPE STRING_TYPE (OPTION_MAP implode (FDline (w2n fd) fs))  x *
                   ROFS (bumpLineFD (w2n fd) fs) * STDOUT out`
  >- ( xapp \\ instantiate \\ xsimpl )
  \\ Cases_on`FDline (w2n fd) fs` \\ fs[FDline_NONE_linesFD]
  \\ fs[ml_translatorTheory.OPTION_TYPE_def]
  \\ xmatch
  \\ rename1`FDline _ _ = SOME ln`
  \\ rveq
  \\ xlet`POSTv bv. &BOOL (m (implode ln)) bv * ROFS (bumpLineFD (w2n fd) fs) * STDOUT out`
  >- ( xapp \\ instantiate \\ xsimpl )
  \\ xlet`POSTv x. ROFS (bumpLineFD (w2n fd) fs) * STDOUT (out ++ (if m (implode ln) then explode pfx ++ ln else ""))`
  >- (
    xif
    >- (
      xlet`POSTv x. ROFS (bumpLineFD (w2n fd) fs) * STDOUT (out ++ explode pfx)`
      >- (xapp \\ instantiate \\ xsimpl
          \\ CONV_TAC(SWAP_EXISTS_CONV) \\ qexists_tac`out`
          \\ xsimpl )
      \\ xapp \\ instantiate \\ xsimpl
      \\ simp[mlstringTheory.explode_implode]
      \\ CONV_TAC(SWAP_EXISTS_CONV) \\ qexists_tac`out ++ explode pfx`
      \\ xsimpl )
    \\ xcon \\ xsimpl )
  \\ imp_res_tac linesFD_eq_cons_imp \\ rveq \\ fs[]
  \\ first_x_assum(qspecl_then[`fd`,`bumpLineFD (w2n fd) fs`]mp_tac)
  \\ simp[] \\ strip_tac
  \\ xapp
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac`out ++ (if m (implode ln) then explode pfx ++ ln else "")`
  \\ fs[] \\ xsimpl
  \\ Cases_on`m (implode ln)` \\ fs[]
  \\ xsimpl);

(* TODO: fix concat_2 problem in mlstringProg *)
val notfound_string_def = Define`
  notfound_string f = concat[strlit"cake_grep: ";f;strlit": No such file or directory\n"]`;

val r = translate notfound_string_def;

val print_matching_lines_in_file = process_topdecs`
  fun print_matching_lines_in_file m file =
    let val fd = FileIO.openIn file
    in (print_matching_lines m (String.concat_2[file,":"]) fd;
        FileIO.close fd)
    end handle FileIO.BadFileName => 
        print_err (notfound_string file)`;
val _ = append_prog print_matching_lines_in_file;

val print_matching_lines_in_file_spec = Q.store_thm("print_matching_lines_in_file_spec",
  `FILENAME f fv ∧
   CARD (FDOM (alist_to_fmap fs.infds)) < 255 ∧
   (STRING_TYPE --> BOOL) m mv
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"print_matching_lines_in_file"(get_ml_prog_state()))
     [mv; fv]
     (ROFS fs * STDOUT out * STDERR err)
     (POSTv uv. &UNIT_TYPE () uv * ROFS fs *
                STDOUT (out ++
                  if inFS_fname fs f then
                    CONCAT
                      (MAP ((++)(explode f ++ ":"))
                        (FILTER (m o implode)
                           (MAP (combin$C (++) "\n")
                             (splitlines (THE (ALOOKUP fs.files f))))))
                  else "") *
                STDERR (err ++
                  if inFS_fname fs f then ""
                  else explode (notfound_string f)))`,
  xcf"print_matching_lines_in_file"(get_ml_prog_state())
  \\ qmatch_goalsub_abbrev_tac`_ * ROFS fs * STDOUT result * STDERR error`
  \\ reverse(xhandle`POST
       (λv. &UNIT_TYPE () v * ROFS fs * STDOUT result * STDERR error)
       (λe. &(BadFileName_exn e ∧ ¬inFS_fname fs f) * ROFS fs * STDOUT out * STDERR err)`)
  >- (
    xcases
    \\ fs[BadFileName_exn_def]
    \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
    \\ xlet`POSTv v. &STRING_TYPE (notfound_string f) v 
                     * ROFS fs * STDOUT out * STDERR err`
    >- ( xapp \\ xsimpl \\ qexists_tac`f` \\ fs[FILENAME_def])
    \\ xapp \\ instantiate \\ xsimpl 
    \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`err`
    \\ xsimpl)
  >- ( xsimpl )
  \\ xlet`POST (λv. &(WORD ((n2w (nextFD fs)):word8) v ∧ validFD (nextFD fs) (openFileFS f fs) ∧
                      inFS_fname fs f) * ROFS (openFileFS f fs) * STDOUT out * STDERR err)
               (λe. &(BadFileName_exn e ∧ ¬inFS_fname fs f) * ROFS fs * STDOUT out * STDERR err)`
  >- ( xapp \\ instantiate \\ xsimpl )
  >- ( xsimpl )
  \\ xlet`POSTv v. &LIST_TYPE STRING_TYPE [] v * ROFS (openFileFS f fs) * STDOUT out * STDERR err`
  >- ( xcon \\ xsimpl \\ fs[ml_translatorTheory.LIST_TYPE_def] )
  \\ xlet`POSTv v. &LIST_TYPE STRING_TYPE [strlit":"] v * ROFS (openFileFS f fs) * STDOUT out * STDERR err`
  >- ( xcon \\ xsimpl \\ fs[ml_translatorTheory.LIST_TYPE_def] )
  \\ xlet`POSTv v. &LIST_TYPE STRING_TYPE [f;strlit":"] v * ROFS (openFileFS f fs) * STDOUT out * STDERR err`
  >- ( xcon \\ xsimpl \\ fs[ml_translatorTheory.LIST_TYPE_def,FILENAME_def] )
  \\ xlet`POSTv v. &STRING_TYPE (concat[f;strlit":"]) v * ROFS (openFileFS f fs) * STDOUT out * STDERR err`
  >- ( xapp \\ instantiate \\ xsimpl )
  \\ xlet`POSTv v. &UNIT_TYPE () v * ROFS (bumpAllFD (nextFD fs) (openFileFS f fs)) 
                                   * STDOUT result * STDERR error`
  \\ fs[] \\ imp_res_tac nextFD_ltX \\ simp[]
  >- (
    xapp
    \\ instantiate
    \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`out`
    \\ xsimpl
    \\ fs[mlstringTheory.concat_thm,mlstringTheory.explode_implode]
    \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS \\ fs[]
    \\ imp_res_tac ALOOKUP_inFS_fname_openFileFS_nextFD
    \\ simp[linesFD_def]
    \\ Cases_on`0 < LENGTH content` \\ fs[libTheory.the_def,LENGTH_NIL]
    \\ xsimpl )
  \\ xapp
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac`bumpAllFD (nextFD fs) (openFileFS f fs)`
  \\ instantiate
  \\ xsimpl
  \\ qmatch_goalsub_abbrev_tac`ROFS fs'`
  \\ `fs' = fs` suffices_by xsimpl
  \\ simp[Abbr`fs'`,RO_fs_component_equality]);

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

val build_matcher_partial_spec = Q.store_thm("build_matcher_partial_spec",
  `REGEXP_REGEXP_TYPE r rv ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"build_matcher"(get_ml_prog_state())) [rv] emp
    (POSTv v. &(STRING_TYPE --> BOOL) (build_matcher r) v)`,
  strip_tac
  \\ rw[app_def]
  \\ irule Arrow_IMP_app_basic
  \\ instantiate
  \\ simp[build_matcher_v_thm]);

val grep = process_topdecs`
  fun grep u =
    case Commandline.arguments ()
    of [] => print_err usage_string
     | [_] => print_err usage_string
     | (regexp::files) =>
       case parse_regexp (String.explode regexp) of
         NONE => print_err (parse_failure_string regexp)
       | SOME r =>
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

val grep_sem_file_def = Define`
  grep_sem_file L fs filename =
    case ALOOKUP fs.files filename of
    | NONE => ("", explode (notfound_string filename) )
    | SOME contents =>
        (CONCAT
          (MAP (λmatching_line. explode filename ++ ":" ++ matching_line ++ "\n")
             (FILTER (λline. line ∈ L) (splitlines contents))), "")`;

val grep_sem_def = Define`
  (grep_sem (_::regexp::filenames) fs =
   if NULL filenames then ("",explode usage_string) else
   case parse_regexp regexp of
   | NONE => ("",explode (parse_failure_string (implode regexp)))
   | SOME r => let l = (MAP (grep_sem_file (regexp_lang r) fs) (MAP implode filenames)) 
                 in (CONCAT (MAP FST l), CONCAT (MAP SND l)))∧
  (grep_sem _ _ = ("",explode usage_string))`;

val grep_termination_assum_def = Define`
  (grep_termination_assum (_::regexp::filenames) ⇔
   if NULL filenames then T else
     case parse_regexp regexp of
     | NONE => T
     | SOME r => IS_SOME (Brz empty [normalize r] (1,singleton (normalize r) 0,[]) MAXNUM_32)) ∧
  (grep_termination_assum _ ⇔ T)`;

val grep_spec = Q.store_thm("grep_spec",
  `cl ≠ [] ∧ EVERY validArg cl ∧ LENGTH (FLAT cl) + LENGTH cl ≤ 256 ∧
   CARD (set (MAP FST fs.infds)) < 255 ∧
   grep_termination_assum cl
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"grep"(get_ml_prog_state()))
    [Conv NONE []]
    (STDOUT out * STDERR err * COMMANDLINE cl * ROFS fs)
    (POSTv v. &UNIT_TYPE () v *
      STDOUT (out ++ FST(grep_sem cl fs))
       * STDERR(err ++ SND(grep_sem cl fs))
          * (COMMANDLINE cl * ROFS fs))`,
  strip_tac
  \\ xcf"grep"(get_ml_prog_state())
  \\ xlet`POSTv v. &UNIT_TYPE () v * STDOUT out * STDERR err * COMMANDLINE cl * ROFS fs`
  >- (xcon \\ xsimpl)
  \\ xlet`POSTv v. &LIST_TYPE STRING_TYPE (TL (MAP implode cl)) v * STDOUT out * STDERR err * COMMANDLINE cl * ROFS fs`
  >- (xapp \\ instantiate \\ xsimpl
      \\ simp[MAP_TL,NULL_EQ,LENGTH_FLAT,MAP_MAP_o,o_DEF] (* TODO: this is duplicated in catProg and bootstrap *)
      \\ Q.ISPECL_THEN[`STRLEN`]mp_tac SUM_MAP_PLUS
      \\ disch_then(qspecl_then[`K 1`,`cl`]mp_tac)
      \\ simp[MAP_K_REPLICATE,SUM_REPLICATE,GSYM LENGTH_FLAT])
  \\ Cases_on`cl` \\ fs[]
  \\ Cases_on`t` \\ fs[ml_translatorTheory.LIST_TYPE_def]
  >- (
    xmatch
    \\ xapp
    \\ simp[grep_sem_def]
    \\ xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`usage_string`
    \\ simp[usage_string_v_thm]
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`err`
    \\ xsimpl 
    )
  \\ rveq
  \\ rename1`EVERY validArg t`
  \\ Cases_on`t` \\ fs[ml_translatorTheory.LIST_TYPE_def]
  >- (
    xmatch
    \\ xapp
    \\ simp[grep_sem_def]
    \\ xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`usage_string`
    \\ simp[usage_string_v_thm]
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`err`
    \\ xsimpl )
  \\ rveq
  \\ xmatch
  \\ rename1`grep_sem (grep::regexp::file1::files)`
  \\ simp[grep_sem_def,MAP_MAP_o,o_DEF]
  \\ qmatch_goalsub_abbrev_tac`COMMANDLINE cl`
  \\ qmatch_assum_abbrev_tac`Abbrev(cl = grep::regexp::fls)`
  \\ xlet`POSTv v. &LIST_TYPE CHAR regexp v * STDOUT out * STDERR err * COMMANDLINE cl * ROFS fs`
  >- (
    xapp
    \\ instantiate
    \\ simp[mlstringTheory.explode_implode]
    \\ xsimpl)
  \\ xlet`POSTv v. &OPTION_TYPE REGEXP_REGEXP_TYPE  (parse_regexp regexp) v * 
          STDOUT out * STDERR err * COMMANDLINE cl * ROFS fs`
  >- ( xapp \\ instantiate \\ xsimpl )
  \\ Cases_on`parse_regexp regexp` \\ fs[ml_translatorTheory.OPTION_TYPE_def]
  >- (
    xmatch
    \\ xlet`POSTv v. &STRING_TYPE (parse_failure_string (implode regexp)) v * 
            STDOUT out * STDERR err * COMMANDLINE cl * ROFS fs`
    >- (xapp \\ instantiate \\ xsimpl )
    \\ xapp
    \\ instantiate
    \\ xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`err`
    \\ xsimpl)
  \\ qmatch_goalsub_abbrev_tac`(out ++ gs1) ++ (FLAT (MAP ff1 files))`
  \\ qmatch_goalsub_abbrev_tac`(err ++ gs2) ++ (FLAT (MAP ff2 files))`
  \\ `(out ++ gs1) ++ (FLAT (MAP ff1 files)) = out ++ FLAT (MAP ff1 fls)`
  by ( unabbrev_all_tac \\ simp[] )
  \\ `(err ++ gs2) ++ (FLAT (MAP ff2 files)) = err ++ FLAT (MAP ff2 fls)`
  by ( unabbrev_all_tac \\ simp[] )
  \\ pop_assum SUBST1_TAC
  \\ simp[Abbr`gs1`,Abbr`ff1`,Abbr`gs2`,Abbr`ff2`]
  \\ xmatch
  \\ rename1`parse_regexp regexp = SOME r`
  \\ xfun_spec`appthis`
     `∀f fv outp erro.
      FILENAME f fv ∧ CARD (FDOM (alist_to_fmap fs.infds)) < 255 ⇒
      app p appthis [fv] (STDOUT outp * STDERR erro * COMMANDLINE cl * ROFS fs)
        (POSTv v. &UNIT_TYPE () v 
                  * STDOUT (outp ++ FST(grep_sem_file (regexp_lang r) fs f)) 
                  * STDERR (erro ++ SND(grep_sem_file (regexp_lang r) fs f)) 
                  * COMMANDLINE cl * ROFS fs)`
  >- (
    rw[]
    \\ first_x_assum match_mp_tac
    \\ xlet`POSTv mv. &(STRING_TYPE --> BOOL) (build_matcher r) mv 
                      * STDOUT outp * STDERR erro * COMMANDLINE cl * ROFS fs`
    >- ( xapp_spec build_matcher_partial_spec \\ instantiate \\ xsimpl )
    \\ xapp
    \\ instantiate
    \\ xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`outp`
    \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`erro`
    \\ xsimpl
    \\ simp[grep_sem_file_def]
    \\ reverse IF_CASES_TAC
    >- (   
        CASE_TAC \\ xsimpl \\ fs[] \\ imp_res_tac ALOOKUP_SOME_inFS_fname
        \\ CASE_TAC \\ xsimpl \\ fs[] \\ imp_res_tac ALOOKUP_SOME_inFS_fname
        \\ simp[notfound_string_def,mlstringTheory.concat_thm,
                mlstringTheory.explode_implode]
        \\ xsimpl
        )
    \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS
    \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`STDOUT (outp ++ s1)`
    \\ qmatch_goalsub_abbrev_tac`STDOUT (outp ++ s2) * _ * _`
    \\ `s1 = s2` suffices_by xsimpl
    \\ simp[Abbr`s1`,Abbr`s2`]
    \\ AP_TERM_TAC
    \\ simp[FILTER_MAP,MAP_MAP_o]
    \\ simp[Once o_DEF]
    \\ AP_TERM_TAC
    \\ AP_THM_TAC
    \\ AP_TERM_TAC
    \\ simp[FUN_EQ_THM,build_matcher_def]
    \\ simp[mlstringTheory.explode_implode]
    \\ simp[mlstringTheory.implode_def]
    \\ simp[FRONT_APPEND]
    \\ simp[match_line_def]
    \\ gen_tac
    \\ fs[Abbr`cl`,grep_termination_assum_def,Abbr`fls`]
    \\ `dom_Brz_alt empty [normalize r]`
    by ( metis_tac[dom_Brz_alt_equal,dom_Brz_def] )
    \\ imp_res_tac regexp_matcher_correct
    \\ TOP_CASE_TAC
    >- (
      fs[regexp_matcher_with_limit_def,compile_regexp_with_limit_def]
      \\ rfs[IS_SOME_EXISTS] \\ rfs[]
      \\ every_case_tac \\ fs[] )
    \\ imp_res_tac regexp_matcher_with_limit_sound
    \\ rveq
    \\ fs[])
  \\ xapp_spec (INST_TYPE[alpha|->``:mlstring``]mllistProgTheory.app_spec)
  \\ CONV_TAC (RESORT_EXISTS_CONV List.rev)
  \\ qexists_tac`λn. 
    STDOUT (out ++ (CONCAT (MAP FST (MAP (grep_sem_file (regexp_lang r) fs) (TAKE n (MAP implode fls)))))) *
    STDERR (err ++ (CONCAT (MAP SND (MAP (grep_sem_file (regexp_lang r) fs) (TAKE n (MAP implode fls)))))) *
    COMMANDLINE cl * ROFS fs`
  \\ xsimpl
  \\ qexists_tac`MAP implode fls`
  \\ qexists_tac`STRING_TYPE`
  \\ reverse conj_tac
  >- ( simp[MAP_MAP_o,o_DEF] \\ xsimpl)
  \\ reverse conj_tac
  >- ( simp[Abbr`fls`,ml_translatorTheory.LIST_TYPE_def] )
  \\ rw[] \\ rfs[EL_MAP]
  \\ qmatch_assum_abbrev_tac`STRING_TYPE f xv`
  \\ `validArg (explode f)`
  by (
    fs[Abbr`fls`,Abbr`f`,mlstringTheory.explode_implode,EVERY_MEM,MEM_EL,PULL_EXISTS]
    \\ Cases_on`n` \\ fs[] )
  \\ `FILENAME f xv`
  by (
    fs[FILENAME_def,commandLineFFITheory.validArg_def,Abbr`f`,mlstringTheory.explode_implode,mlstringTheory.implode_def]
    \\ fs[EVERY_MEM] )
  \\ first_x_assum drule
  \\ `TAKE (n+1) fls = (TAKE n fls) ++ [EL n fls]` by ( simp[TAKE_EL_SNOC] )
  \\ simp[GSYM MAP_TAKE]
  \\ simp[MAP_MAP_o]
  \\ simp[set_sepTheory.STAR_ASSOC]
  );

val st = get_ml_prog_state()
val name = "grep"
val spec = grep_spec |> UNDISCH |> ioProgLib.add_basis_proj
val (sem_thm,prog_tm) = ioProgLib.call_thm st name spec

val grep_prog_def = Define`grep_prog = ^prog_tm`;

val grep_semantics = save_thm("grep_semantics",
  sem_thm
  |> REWRITE_RULE[GSYM grep_prog_def]
  |> DISCH_ALL
  |> REWRITE_RULE[AND_IMP_INTRO]
  |> CONV_RULE(LAND_CONV EVAL)
  |> REWRITE_RULE[APPEND]);

val _ = export_theory ();
