open preamble ml_translatorLib ml_progLib
     cfTacticsLib basisFunctionsLib
     rofsFFITheory mlfileioProgTheory ioProgTheory
     charsetTheory diffTheory mlstringTheory

val _ = new_theory "patchProg";

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

(* TODO: a better version of num_from_dec_string should be in the basis library, Int.fromString *)

(* Circumvents a problem where the translator generates unprovable side conditions
   for higher-order functions *)
val unhex_all_def = Define `(unhex_all [] = []) /\ (unhex_all (a::b) = UNHEX a::unhex_all b)`

val unhex_map = Q.prove(`!s. unhex_all s = MAP UNHEX s`, Induct >> fs[unhex_all_def])

val s2n_UNHEX_def = Define `s2n_UNHEX b s = l2n b (unhex_all (REVERSE s))`

val num_from_dec_string_thm = Q.store_thm("num_from_dec_string_thm",
  `!s. toNum s = s2n_UNHEX 10 s`,
  rw[ASCIInumbersTheory.num_from_dec_string_def,s2n_UNHEX_def,ASCIInumbersTheory.s2n_def,
     unhex_map]);

val _ = translate num_from_dec_string_thm;

val l2n_side_IMP = Q.prove(`∀n l. n <> 0 ==> l2n_side n l = T`,
  strip_tac >> Induct >> rw[Once(fetch "-" "l2n_side_def")]);

val unhex_side = Q.prove(`!c. unhex_side c <=> isHexDigit c`,
  Cases >> fs[isHexDigit_def] >> PURE_ONCE_REWRITE_TAC[fetch "-" "unhex_side_def"]
        >> PURE_REWRITE_TAC[AC DISJ_ASSOC DISJ_COMM]
        >> PURE_REWRITE_TAC [GSYM DISJ_ASSOC,AND_CLAUSES]
        >> PURE_ONCE_REWRITE_TAC[EQ_IMP_THM]
        >> rpt strip_tac >> rfs[CHR_11]) |> update_precondition

val unhex_all_side = Q.prove(`!s. unhex_all_side s <=> EVERY isHexDigit s`,
  Induct >> PURE_ONCE_REWRITE_TAC[fetch "-" "unhex_all_side_def"]>> fs[unhex_side])
  |> update_precondition;

val s2n_unhex_side_IMP = Q.prove(`∀n s. n <> 0 ==> s2n_unhex_side n s = EVERY isHexDigit s`,
  rpt strip_tac
  >> rw[Once(fetch "-" "s2n_unhex_side_def"),l2n_side_IMP,unhex_all_side,EVERY_REVERSE]);

val num_from_dec_string_side = Q.prove(`
  ∀s. num_from_dec_string_side s = EVERY isHexDigit s`,
  fs[fetch "-" "num_from_dec_string_side_def",s2n_unhex_side_IMP]) |> update_precondition;

val _ = translate parse_patch_header_def;

val tokens_less_eq = Q.prove(`!s f. EVERY (\x. strlen x <= strlen s) (tokens f s)`,
  Induct >> Ho_Rewrite.PURE_ONCE_REWRITE_TAC[SWAP_FORALL_THM]
  >> PURE_ONCE_REWRITE_TAC[TOKENS_eq_tokens_sym]
  >> recInduct TOKENS_ind >> rpt strip_tac
  >> fs[TOKENS_def] >> pairarg_tac >> reverse(Cases_on `l`) >> rw[]
  >- (drule SPLITP_JOIN >> fs[implode_def,strlen_def])
  >> fs[SPLITP_NIL_FST,SPLITP] >> every_case_tac >> fs[]
  >- (`!x. (λx. strlen x <= STRLEN r) x ==> (λx. strlen x <= SUC (STRLEN t)) x`
       by(rpt strip_tac >> PURE_ONCE_REWRITE_TAC[SPLITP_LENGTH] >> fs[])
       >> drule EVERY_MONOTONIC >> pop_assum kall_tac >> disch_then match_mp_tac >> rw[])
  >> `!x. (λx. strlen x <= STRLEN t) x ==> (λx. strlen x <= SUC (STRLEN t)) x` by fs[]
  >> drule EVERY_MONOTONIC >> pop_assum kall_tac >> disch_then match_mp_tac >> rw[]);

val tokens_sum_less_eq = Q.prove(`!s f. SUM(MAP strlen (tokens f s)) <= strlen s`,
  Induct >> Ho_Rewrite.PURE_ONCE_REWRITE_TAC[SWAP_FORALL_THM]
  >> PURE_REWRITE_TAC[TOKENS_eq_tokens_sym,explode_thm,MAP_MAP_o]
  >> recInduct TOKENS_ind >> rpt strip_tac
  >> fs[TOKENS_def] >> pairarg_tac >> fs[] >> Cases_on `l` >> rw[] >> rfs[]
  >> fs[SPLITP_NIL_FST] >> fs[SPLITP] >> every_case_tac
  >> fs[] >> rveq
  >> CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[SPLITP_LENGTH])) >> fs[]);

val tokens_not_nil = Q.prove(`!s f. EVERY (\x. x <> strlit "") (tokens f s)`,
  Induct >> Ho_Rewrite.PURE_ONCE_REWRITE_TAC[SWAP_FORALL_THM]
  >> PURE_REWRITE_TAC[TOKENS_eq_tokens_sym,explode_thm]
  >> recInduct TOKENS_ind >> rpt strip_tac
  >> rw[TOKENS_def] >> pairarg_tac >> fs[] >> reverse(Cases_on `l`)
  >> fs[implode_def]);

val tokens_two_less = Q.prove(`!s f s1 s2. tokens f s = [s1;s2] ==> strlen s1 < strlen s /\ strlen s2 < strlen s`,
  ntac 2 strip_tac >> qspecl_then [`s`,`f`] assume_tac tokens_sum_less_eq
  >> qspecl_then [`s`,`f`] assume_tac tokens_not_nil
  >> Induct >> Cases >> Induct >> Cases >> rpt strip_tac >> fs[]);

val hexDigit_IMP_digit = Q.store_thm("hexDigit_IMP_digit",`!c. isDigit c ==> isHexDigit c`,
  rw[isHexDigit_def,isDigit_def]);

val parse_patch_header_side = Q.prove(`!s. parse_patch_header_side s = T`,
  rw[fetch "-" "parse_patch_header_side_def",
     fetch "-" "num_from_string_side_def",
     fetch "-" "fromstring_side_def"]
  >> TRY(match_mp_tac(MATCH_MP EVERY_MONOTONIC hexDigit_IMP_digit) >> fs[string_is_num_def])
  >> TRY(match_mp_tac hexDigit_IMP_digit >> fs[string_is_num_def])
  >> metis_tac[tokens_two_less]) |> update_precondition;

val r = save_thm("patch_aux_ind",
  patch_aux_ind |> REWRITE_RULE (map GSYM [mllistTheory.take_def,
                                           mllistTheory.drop_def]));
val _ = add_preferred_thy"-";
val _ = translate(patch_aux_def |> REWRITE_RULE (map GSYM [mllistTheory.take_def,
                                                           mllistTheory.drop_def]));

val _ = translate patch_alg_def;

val notfound_string_def = Define`
  notfound_string f = concat[strlit"cake_patch: ";f;strlit": No such file or directory\n"]`;

val r = translate notfound_string_def;

val usage_string_def = Define`
  usage_string = strlit"Usage: patch <file> <patch>\n"`;

val r = translate usage_string_def;

val rejected_patch_string_def = Define`
  rejected_patch_string = strlit"cake_patch: Patch rejected\n"`;

val r = translate rejected_patch_string_def;

val _ = (append_prog o process_topdecs) `
  fun patch' fname1 fname2 =
    case FileIO.inputLinesFrom fname1 of
        NONE => print_err (notfound_string fname1)
      | SOME lines1 =>
        case FileIO.inputLinesFrom fname2 of
            NONE => print_err (notfound_string fname2)
          | SOME lines2 =>
            case patch_alg lines2 lines1 of
                NONE => print_err (rejected_patch_string)
              | SOME s => List.app print s`

(* TODO: copypasta from diffProgScript, should be elsewhere *)
val take_add_one_lemma = Q.prove(
  `!n l. n < LENGTH l ==> TAKE (n+1) l = TAKE n l ++ [EL n l]`,
  Induct >> Cases >> fs[TAKE] >> fs[ADD1]);

val patch'_spec = Q.store_thm("patch'_spec",
  `FILENAME f1 fv1 ∧ FILENAME f2 fv2 /\
   CARD (FDOM (alist_to_fmap fs.infds)) < 255
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"patch'"(get_ml_prog_state()))
     [fv1; fv2]
     (ROFS fs * STDOUT out * STDERR err)
     (POSTv uv. &UNIT_TYPE () uv
                * ROFS fs *
                STDOUT (out ++
                        if inFS_fname fs f1 /\ inFS_fname fs f2 then
                          case patch_alg (all_lines fs f2) (all_lines fs f1) of
                              NONE => ""
                            | SOME s => CONCAT (MAP explode s)
                  else "") *
                STDERR (err ++
                   if inFS_fname fs f1 /\ inFS_fname fs f2
                      /\ IS_SOME(patch_alg (all_lines fs f2) (all_lines fs f1)) then ""
                  else if ¬(inFS_fname fs f1) then explode (notfound_string f1)
                  else if ¬(inFS_fname fs f2) then explode (notfound_string f2)
                  else explode rejected_patch_string))
`,
  xcf"patch'"(get_ml_prog_state())
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
  \\ xlet `POSTv sv. &OPTION_TYPE (LIST_TYPE STRING_TYPE) (patch_alg
                                      (all_lines fs f2)
                                      (all_lines fs f1)) sv
                * ROFS fs * STDOUT out * STDERR err`
  >- (xapp \\ instantiate \\ xsimpl)
  \\ qpat_abbrev_tac `a1 = patch_alg _ _`
  \\ Cases_on `a1` \\ fs[ml_translatorTheory.OPTION_TYPE_def]
  \\ xmatch
  >- (xapp \\ assume_tac(theorem "rejected_patch_string_v_thm") \\ instantiate
      \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `err` \\ xsimpl)
  \\ xapp_spec (INST_TYPE [alpha |-> ``:mlstring``] mllistProgTheory.app_spec)
  \\ qexists_tac `emp` \\ qexists_tac `x`
  \\ qexists_tac `\n. ROFS fs * STDOUT(out ++ CONCAT(TAKE n (MAP explode x))) * STDERR err`
  \\ xsimpl \\ fs[GSYM MAP_TAKE] \\ xsimpl \\ instantiate \\ rpt strip_tac
  \\ xapp \\ instantiate \\ xsimpl \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac `STRCAT out (CONCAT (MAP explode (TAKE n x)))` \\ xsimpl
  \\ imp_res_tac take_add_one_lemma \\ fs[] \\ xsimpl);

val _ = (append_prog o process_topdecs) `
  fun patch u =
    case Commandline.arguments () of
        (f1::f2::[]) => patch' f1 f2
      | _ => print_err usage_string`

val patch_spec = Q.store_thm("patch_spec",
  `CARD (set (MAP FST fs.infds)) < 255
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"patch"(get_ml_prog_state()))
     [Conv NONE []]
     (ROFS fs * STDOUT out * STDERR err * COMMANDLINE cl)
     (POSTv uv. &UNIT_TYPE () uv
                *
                STDOUT (out ++
                   if (LENGTH cl = 3) /\ inFS_fname fs (implode (EL 1 cl)) /\ inFS_fname fs (implode (EL 2 cl)) then
                   case patch_alg (all_lines fs (implode (EL 2 cl)))
                                  (all_lines fs (implode (EL 1 cl))) of
                     NONE => ""
                   | SOME s => CONCAT (MAP explode s)
                  else "") *
                STDERR (err ++
                  if (LENGTH cl = 3) /\ inFS_fname fs (implode (EL 1 cl))
                     /\ inFS_fname fs (implode (EL 2 cl))
                     /\ IS_SOME (patch_alg (all_lines fs (implode (EL 2 cl)))
                                            (all_lines fs (implode (EL 1 cl)))) then ""
                  else if LENGTH cl <> 3 then explode (usage_string)
                  else if ¬(inFS_fname fs (implode (EL 1 cl))) then explode (notfound_string (implode (EL 1 cl)))
                  else if ¬(inFS_fname fs (implode (EL 2 cl))) then explode (notfound_string (implode (EL 2 cl)))
                  else explode (rejected_patch_string)) * (COMMANDLINE cl * ROFS fs))`,
  strip_tac \\ xcf "patch" (get_ml_prog_state())
  \\ xlet `POSTv v. &UNIT_TYPE () v * ROFS fs * STDOUT out * STDERR err * COMMANDLINE cl`
  >- (xcon \\ xsimpl)
  \\ reverse(Cases_on`wfcl cl`) >- (fs[mlcommandLineProgTheory.COMMANDLINE_def] \\ xpull)
  \\ fs[mlcommandLineProgTheory.wfcl_def]
  \\ xlet`POSTv v. &LIST_TYPE STRING_TYPE (TL (MAP implode cl)) v * ROFS fs * STDOUT out * STDERR err * COMMANDLINE cl`
  >- (xapp \\ xsimpl \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`cl` \\ xsimpl)
  \\ Cases_on `cl` \\ fs[]
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
  \\ xapp
  \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `out`
  \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `fs`
  \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `implode h''`
  \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `implode h'`
  \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `err`
  \\ xsimpl \\ fs[FILENAME_def,mlstringTheory.explode_implode]
  \\ fs[mlstringTheory.implode_def,mlstringTheory.strlen_def]
  \\ fs[commandLineFFITheory.validArg_def,EVERY_MEM]);

val st = get_ml_prog_state();

val name = "patch"
val spec = patch_spec |> UNDISCH |> ioProgLib.add_basis_proj
val (sem_thm,prog_tm) = ioProgLib.call_thm st name spec

val patch_prog_def = Define`patch_prog = ^prog_tm`;

val patch_semantics = save_thm("patch_semantics",
  sem_thm
  |> REWRITE_RULE[GSYM patch_prog_def]
  |> DISCH_ALL
  |> ONCE_REWRITE_RULE[AND_IMP_INTRO]
  |> CONV_RULE(LAND_CONV EVAL)
  |> SIMP_RULE(srw_ss())[]);

val _ = export_theory ();
