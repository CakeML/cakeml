open HolKernel boolLib bossLib

open pred_setTheory
open mmlPEGTheory gramTheory gramPropsTheory
open lcsymtacs boolSimps
open parsingPreamble

open pegSoundTheory

val _ = new_theory "pegComplete"

val _ = augment_srw_ss [rewrites [
  peg_eval_seql_CONS, peg_eval_tok_SOME, tokeq_def, bindNT_def, mktokLf_def,
  peg_eval_choicel_CONS, pegf_def, peg_eval_seq_SOME, pnt_def, peg_eval_try,
  try_def]]

val has_length = assert (can (find_term (same_const listSyntax.length_tm)) o
                         concl)

val peg_eval_choice_NONE =
  ``peg_eval G (i, choice s1 s2 f) NONE``
    |> SIMP_CONV (srw_ss()) [Once pegTheory.peg_eval_cases]

val peg_eval_tok_NONE =
  ``peg_eval G (i, tok P f) NONE``
    |> SIMP_CONV (srw_ss()) [Once pegTheory.peg_eval_cases]

val peg_eval_seq_NONE =
  ``peg_eval G (i, seq s1 s2 f) NONE``
    |> SIMP_CONV (srw_ss()) [Once pegTheory.peg_eval_cases]

val disjImpI = prove(``~p \/ q ⇔ p ⇒ q``, DECIDE_TAC)

val ptree_head_eq_tok0 = prove(
  ``(ptree_head pt = TOK tk) ⇔ (pt = Lf (TOK tk))``,
  Cases_on `pt` >> simp[]);
val ptree_head_eq_tok = save_thm(
  "ptree_head_eq_tok",
  CONJ ptree_head_eq_tok0
       (CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ)) ptree_head_eq_tok0))
val _ = export_rewrites ["ptree_head_eq_tok"]

val firstSet_def = Define`
  firstSet G sf = { t | ∃rest. derives G sf (TOK t :: rest) }
`;

val firstSet_nonempty_fringe = store_thm(
  "firstSet_nonempty_fringe",
  ``∀pt t rest. ptree_fringe pt = TOK t :: rest ∧ valid_ptree G pt ⇒
                t ∈ firstSet G [ptree_head pt]``,
  simp[firstSet_def] >> metis_tac [grammarTheory.valid_ptree_derive]);

val IN_firstSet = store_thm(
  "IN_firstSet",
  ``t ∈ firstSet G [sym] ⇒
    ∃pt rest. ptree_head pt = sym ∧ valid_ptree G pt ∧
              ptree_fringe pt = TOK t :: rest``,
  simp[firstSet_def] >>
  metis_tac [grammarTheory.ptrees_derive_extensible
               |> Q.SPECL [`Lf sym`, `TOK t :: rest`]
               |> SIMP_RULE (srw_ss()) []]);

val derives_preserves_leading_toks = store_thm(
  "derives_preserves_leading_toks",
  ``∀G syms rest x.
        derives G (MAP TOK syms ++ rest) x ⇔
        ∃rest'. derives G rest rest' ∧ x = MAP TOK syms ++ rest'``,
  rpt gen_tac >> eq_tac
  >- (`∀x y. derives G x y ⇒
             ∀syms rest.
               (x = MAP TOK syms ++ rest) ⇒
               ∃rest'. derives G rest rest' ∧ y = MAP TOK syms ++ rest'`
        suffices_by metis_tac[] >>
      ho_match_mp_tac relationTheory.RTC_INDUCT >> rw[] >>
      fs[grammarTheory.derive_def] >> rveq >>
      qpat_assum `MAP TOK syms ++ rest = Y` mp_tac >>
      dsimp[listTheory.APPEND_EQ_APPEND, MAP_EQ_APPEND, MAP_EQ_CONS,
            listTheory.APPEND_EQ_SING] >> rw[] >>
      first_x_assum (qspec_then `syms` mp_tac) >>
      simp_tac bool_ss [listTheory.APPEND_11, GSYM APPEND_ASSOC] >>
      rw[] >>
      metis_tac [grammarTheory.derive_def, relationTheory.RTC_CASES1,
                 listTheory.APPEND]) >>
  rw[] >> match_mp_tac grammarTheory.derives_paste_horizontally >>
  simp[]);

val firstSet_NIL = Store_thm(
  "firstSet_NIL",
  ``firstSet G [] = {}``,
  simp[firstSet_def] >> simp[Once relationTheory.RTC_CASES1] >>
  simp[grammarTheory.derive_def]);

val firstSet_TOK = store_thm(
  "firstSet_TOK",
  ``firstSet G (TOK t::rest) = {t}``,
  simp[firstSet_def, EXTENSION, EQ_IMP_THM] >> rw[]
  >- (qspecl_then [`G`, `[t]`, `rest`] mp_tac derives_preserves_leading_toks >>
      simp[] >> strip_tac >> fs[]) >>
  metis_tac[relationTheory.RTC_REFL]);
val _ = export_rewrites ["firstSet_TOK"]

val derives_leading_nonNT_E = store_thm(
  "derives_leading_nonNT_E",
  ``N ∉ FDOM G.rules ∧ derives G (NT N :: rest) Y ⇒
    ∃rest'. Y = NT N :: rest' ∧ derives G rest rest'``,
  `∀X Y. derives G X Y ⇒
         ∀N rest. N ∉ FDOM G.rules ∧ X = NT N :: rest ⇒
                  ∃rest'. Y = NT N :: rest' ∧ derives G rest rest'`
    suffices_by metis_tac[] >>
  ho_match_mp_tac relationTheory.RTC_INDUCT >> simp[] >> rw[] >>
  fs[grammarTheory.derive_def, Once listTheory.APPEND_EQ_CONS] >>
  fs[listTheory.APPEND_EQ_CONS] >> rw[] >> fs[] >>
  match_mp_tac (relationTheory.RTC_RULES |> SPEC_ALL |> CONJUNCT2) >>
  metis_tac [grammarTheory.derive_def]);

val derives_leading_nonNT = store_thm(
  "derives_leading_nonNT",
  ``N ∉ FDOM G.rules ⇒
    (derives G (NT N :: rest) Y ⇔
     ∃rest'. Y = NT N :: rest' ∧ derives G rest rest')``,
  strip_tac >> eq_tac >- metis_tac [derives_leading_nonNT_E] >>
  rw[] >>
  metis_tac [listTheory.APPEND, grammarTheory.derives_paste_horizontally,
             relationTheory.RTC_REFL]);

val derives_split_horizontally = store_thm(
  "derives_split_horizontally",
  ``∀X Y Z. derives G (X ++ Y) Z ⇒
            ∃Z1 Z2. derives G X Z1 ∧ derives G Y Z2 ∧ (Z = Z1 ++ Z2)``,
  `∀X0 Z. derives G X0 Z ⇒
          ∀X Y. X0 = X ++ Y ⇒
                ∃Z1 Z2. derives G X Z1 ∧ derives G Y Z2 ∧ (Z = Z1 ++ Z2)`
    suffices_by metis_tac[] >>
  ho_match_mp_tac relationTheory.RTC_INDUCT >> simp[] >> conj_tac
  >- metis_tac [relationTheory.RTC_REFL] >>
  rpt strip_tac >> fs[grammarTheory.derive_def] >> rveq >>
  asm_match `X ++ Y = p ++ [NT sym] ++ s` >>
  `(∃l. X = p ++ [NT sym] ++ l ∧ s = l ++ Y) ∨
   (∃l. Y = l ++ [NT sym] ++ s ∧ p = X ++ l)`
     by (first_x_assum (mp_tac o
                        SIMP_RULE (srw_ss()) [listTheory.APPEND_EQ_APPEND] o
                        assert (is_eq o concl)) >> rw[] >>
         fs[listTheory.APPEND_EQ_CONS]) >>
  rw[] >>
  PROVE_TAC[relationTheory.RTC_REFL, relationTheory.RTC_CASES1,
            APPEND_ASSOC, grammarTheory.derive_def])

val firstSet_NT = store_thm(
  "firstSet_NT",
  ``firstSet G (NT N :: rest) =
      if N ∈ FDOM G.rules then
        BIGUNION (IMAGE (firstSet G) (G.rules ' N)) ∪
        (if nullable G [NT N] then firstSet G rest
         else {})
      else {}``,
  reverse (Cases_on `N ∈ FDOM G.rules`)
  >- simp[firstSet_def, derives_leading_nonNT] >>
  simp[Once EXTENSION] >> qx_gen_tac `t` >> reverse eq_tac
  >- (dsimp[] >> rw[] >> fs[firstSet_def]
      >- (asm_match `rhs ∈ G.rules ' N` >>
          asm_match `derives G rhs (TOK t :: rest0)` >>
          qexists_tac`rest0 ++ rest` >>
          match_mp_tac (relationTheory.RTC_RULES |> SPEC_ALL |> CONJUNCT2) >>
          qexists_tac `rhs ++ rest` >> simp[grammarTheory.derive_def] >>
          metis_tac [listTheory.APPEND, APPEND_ASSOC,
                     grammarTheory.derives_paste_horizontally,
                     relationTheory.RTC_REFL]) >>
      fs[NTpropertiesTheory.nullable_def] >>
      metis_tac [listTheory.APPEND,
                 grammarTheory.derives_paste_horizontally]) >>
  dsimp[firstSet_def] >> qx_gen_tac `rest'` >> strip_tac >>
  `∃Z1 Z2. derives G [NT N] Z1 ∧ derives G rest Z2 ∧
           (TOK t :: rest' = Z1 ++ Z2)`
    by metis_tac [derives_split_horizontally, listTheory.APPEND] >>
  Cases_on `Z1`
  >- (`nullableNT G N` by fs[NTpropertiesTheory.nullable_def] >>
      fs[] >> metis_tac[]) >>
  fs[] >> rveq >>
  qpat_assum `derives G [NT N] X`
    (mp_tac o ONCE_REWRITE_RULE [relationTheory.RTC_CASES1]) >>
  simp[] >> metis_tac[]);

val firstSet_nTyVarList = store_thm(
  "firstSet_nTyVarList",
  ``firstSet mmlG [NT (mkNT nTyVarList)] = { TyvarT s | T }``,
  dsimp[EXTENSION, EQ_IMP_THM] >> rpt strip_tac
  >- (imp_res_tac IN_firstSet >>
      qpat_assum `X IN Y` kall_tac >>
      rpt (pop_assum mp_tac) >> map_every qid_spec_tac [`rest`, `pt`] >>
      ho_match_mp_tac grammarTheory.ptree_ind >>
      simp[cmlG_applied, cmlG_FDOM, MAP_EQ_CONS] >>
      rpt strip_tac >> rveq >> fs[] >> rveq >> simp[] >>
      fs[listTheory.APPEND_EQ_CONS]
      >- (asm_match `ptree_head pt = NN nTyvarN` >>
          Cases_on `pt` >> fs[] >> rw[] >>
          fs[cmlG_FDOM, cmlG_applied, MAP_EQ_CONS] >> rw[] >> fs[] >> rw[]) >>
      rw[] >> asm_match `ptree_head pt = NN nTyVarList` >>
      `0 < LENGTH (ptree_fringe pt)`
        by metis_tac [fringe_length_not_nullable,
                      nullable_TyVarList] >>
      pop_assum mp_tac >> simp[]) >>
  simp[firstSet_def] >> qexists_tac `[]` >>
  match_mp_tac (relationTheory.RTC_RULES |> SPEC_ALL |> CONJUNCT2)>>
  qexists_tac `[NN nTyvarN]` >>
  simp[grammarTheory.derive_def, cmlG_applied, cmlG_FDOM]);

val firstSet_nUQTyOp = store_thm(
  "firstSet_nUQTyOp",
  ``firstSet mmlG [NT (mkNT nUQTyOp)] = { AlphaT l | T } ∪ { SymbolT l | T }``,
  dsimp[EXTENSION, EQ_IMP_THM, firstSet_def] >> rpt conj_tac >>
  simp[Once relationTheory.RTC_CASES1, cmlG_applied, cmlG_FDOM] >>
  dsimp[]);

val firstSet_nStructure = Store_thm(
  "firstSet_nStructure",
  ``firstSet mmlG [NT (mkNT nStructure)] = {StructureT}``,
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied]);

val firstSet_nTypeDec = Store_thm(
  "firstSet_nTypeDec",
  ``firstSet mmlG [NT (mkNT nTypeDec)] = {DatatypeT}``,
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied]);

val firstSet_nDecl = Store_thm(
  "firstSet_nDecl",
  ``firstSet mmlG [NT (mkNT nDecl)] = {ValT; FunT; DatatypeT}``,
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied,
       INSERT_UNION_EQ]);

val firstSet_nTopLevelDec = Store_thm(
  "firstSet_nTopLevelDec",
  ``firstSet mmlG [NT (mkNT nTopLevelDec)] =
    {ValT; FunT; DatatypeT; StructureT}``,
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied, INSERT_UNION_EQ, INSERT_COMM]);

val mmlPEG_total =
    pegTheory.peg_eval_total |> Q.GEN `G` |> Q.ISPEC `mmlPEG`
                             |> C MATCH_MP PEG_wellformed

val nVlist1_expr =
    ``nt (mkNT nVlist1) I ∈ Gexprs mmlPEG``
      |> SIMP_CONV (srw_ss()) [PEG_exprs] |> EQT_ELIM

val peg_respects_firstSets = store_thm(
  "peg_respects_firstSets",
  ``∀N i0 t.
      t ∉ firstSet mmlG [NT N] ∧ ¬peg0 mmlPEG (nt N I) ∧
      nt N I ∈ Gexprs mmlPEG ⇒
      peg_eval mmlPEG (t::i0, nt N I) NONE``,
  rpt gen_tac >> CONV_TAC CONTRAPOS_CONV >> simp[] >>
  Cases_on `nt N I ∈ Gexprs mmlPEG` >> simp[] >>
  IMP_RES_THEN (qspec_then `t::i0` (qxchl [`r`] assume_tac)) mmlPEG_total >>
  pop_assum (assume_tac o MATCH_MP (CONJUNCT1 pegTheory.peg_deterministic)) >>
  simp[] >>
  `r = NONE ∨ ∃i ptl. r = SOME(i,ptl)`
    by metis_tac[optionTheory.option_CASES, pairTheory.pair_CASES] >>
  simp[] >> rveq >>
  `∃pt. ptl = [pt] ∧ ptree_head pt = NT N ∧ valid_ptree mmlG pt ∧
        MAP TK (t::i0) = ptree_fringe pt ++ MAP TK i`
    by metis_tac [peg_sound] >>
  rveq >> Cases_on `peg0 mmlPEG (nt N I)` >> simp[] >>
  `LENGTH i < LENGTH (t::i0)` by metis_tac [not_peg0_LENGTH_decreases] >>
  `ptree_fringe pt = [] ∨ ∃tk rest. ptree_fringe pt = TK tk:: MAP TK rest`
    by (Cases_on `ptree_fringe pt` >> simp[] >> fs[] >> rveq >>
        fs[MAP_EQ_APPEND] >> metis_tac[])
  >- (fs[] >> pop_assum kall_tac >>
      first_x_assum (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  fs[] >> rveq >> metis_tac [firstSet_nonempty_fringe])

val sym2peg_def = Define`
  sym2peg (TOK tk) = tokeq tk ∧
  sym2peg (NT N) = nt N I
`;

val not_peg0_peg_eval_NIL_NONE = store_thm(
  "not_peg0_peg_eval_NIL_NONE",
  ``¬peg0 G sym ∧ sym ∈ Gexprs G ∧ wfG G ⇒
    peg_eval G ([], sym) NONE``,
  strip_tac >>
  `∃r. peg_eval G ([], sym) r`
    by metis_tac [pegTheory.peg_eval_total] >>
  Cases_on `r` >> simp[] >> Cases_on `x` >>
  erule mp_tac not_peg0_LENGTH_decreases >> simp[]);

val list_case_lemma = prove(
  ``([x] = case a of [] => [] | h::t => f h t) ⇔
    (a ≠ [] ∧ [x] = f (HD a) (TL a))``,
  Cases_on `a` >> simp[]);

val left_insert_def = Define`
  (left_insert (Lf x) p sep c = Lf x) ∧
  (left_insert (Nd n subs) p sep c =
     if n <> p then Nd n subs
     else
       case subs of
           [c0] => Nd p [Nd p [c]; sep; c0]
         | [p'; s'; c'] => Nd p [left_insert p' p sep c; s'; c']
         | _ => Nd p subs)
`;

val lassoc_reassociated = store_thm(
  "lassoc_reassociated",
  ``∀G P SEP C ppt spt cpt pf sf cf.
      G.rules ' P = {[NT P; SEP; C]; [C]} ⇒
      valid_ptree G ppt ∧ ptree_head ppt = NT P ∧
      ptree_fringe ppt = MAP TOK pf ∧
      valid_ptree G spt ∧ ptree_head spt = SEP ∧ ptree_fringe spt = MAP TOK sf ∧
      valid_ptree G cpt ∧ ptree_head cpt = C ∧ ptree_fringe cpt = MAP TOK cf ⇒
      ∃cpt' spt' ppt'.
        valid_ptree G ppt' ∧ ptree_head ppt' = NT P ∧
        valid_ptree G spt' ∧ ptree_head spt' = SEP ∧
        valid_ptree G cpt' ∧ ptree_head cpt' = C ∧
        ptree_fringe cpt' ++ ptree_fringe spt' ++ ptree_fringe ppt' =
        MAP TOK (pf ++ sf ++ cf) ∧
        Nd P [ppt; spt; cpt] = left_insert ppt' P spt' cpt'``,
  rpt gen_tac >> strip_tac >>
  map_every qid_spec_tac [`cf`, `sf`, `pf`, `cpt`, `spt`, `ppt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >> simp[MAP_EQ_SING] >>
  qx_gen_tac `subs` >> strip_tac >> simp[MAP_EQ_CONS] >>
  reverse (rpt strip_tac) >> rveq >> fs[]
  >- (qpat_assum `!x. PP x` kall_tac >>
      asm_match `ptree_fringe c0pt = MAP TOK pf` >>
      map_every qexists_tac [`c0pt`, `spt`, `Nd P [cpt]`] >>
      simp[left_insert_def]) >>
  asm_match `ptree_head ppt = NT P` >>
  asm_match `ptree_head s0pt = ptree_head spt` >>
  asm_match `ptree_head c0pt = ptree_head cpt` >>
  fs [MAP_EQ_APPEND] >> rveq >>
  asm_match `ptree_fringe ppt = MAP TOK pf` >>
  asm_match `ptree_fringe s0pt = MAP TOK sf0` >>
  asm_match `ptree_fringe c0pt = MAP TOK cf0` >>
  first_x_assum (fn th =>
    first_x_assum (qspec_then `ppt` mp_tac) >>
    mp_tac (assert (is_forall o concl) th)) >>
  simp[] >> simp[DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
  disch_then (qspecl_then [`s0pt`, `c0pt`, `pf`, `sf0`, `cf0`] mp_tac) >>
  simp[] >>
  disch_then (qxchl [`cpt'`, `spt'`, `ppt'`] strip_assume_tac) >>
  map_every qexists_tac [`cpt'`, `spt'`, `Nd P [ppt'; spt; cpt]`] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, left_insert_def])

val left_insert_mk_linfix = store_thm(
  "left_insert_mk_linfix",
  ``left_insert (mk_linfix N acc arg) N s c =
    mk_linfix N (left_insert acc N s c) arg``,
  qid_spec_tac `acc` >> completeInduct_on `LENGTH arg` >> rw[] >>
  full_simp_tac (srw_ss() ++ DNF_ss)[] >>
  `arg = [] ∨ ∃h1 t. arg = h1::t` by (Cases_on `arg` >> simp[])
  >- simp[mk_linfix_def] >>
  `t = [] ∨ ∃h2 t2. t = h2::t2` by (Cases_on `t` >> simp[])
  >- simp[mk_linfix_def] >>
  rw[] >> simp[mk_linfix_def, left_insert_def]);

val REVERSE_11 = store_thm(
  "REVERSE_11",
  ``(REVERSE l1 = REVERSE l2) ⇔ (l1 = l2)``,
  METIS_TAC [listTheory.REVERSE_REVERSE])
val _ = export_rewrites ["REVERSE_11"]

(* could generalise this slightly: allowing for nullable seps, but this would
   require a more complicated condition on the sfx, something like
     (sfx ≠ [] ∧ ¬nullable mmlG [SEP] ⇒ HD sfx ∉ firstSet mmlG [SEP]) ∧
     (sfx ≠ [] ∧ nullable mmlG [SEP] ⇒ HD sfx ∉ firstSet mmlG [C])
   and I can't be bothered with that right now. *)

val peg_linfix_complete = store_thm(
  "peg_linfix_complete",
  ``(∀n. SEP = NT n ⇒ nt n I ∈ Gexprs mmlPEG) ∧
    ¬peg0 mmlPEG (sym2peg C) ∧ ¬nullable mmlG [C] ∧
    ¬peg0 mmlPEG (sym2peg SEP) ∧ ¬nullable mmlG [SEP] ∧
    mmlG.rules ' (mkNT P) = { [NT (mkNT P); SEP; C] ; [C] } ∧
    (∀pt pfx0 sfx.
       LENGTH pfx0 < LENGTH master ∧
       valid_ptree mmlG pt ∧ ptree_head pt ∈ {SEP; C} ∧
       ptree_fringe pt = MAP TOK pfx0 ⇒
       peg_eval mmlPEG (pfx0 ++ sfx, sym2peg (ptree_head pt))
                       (SOME(sfx,[pt]))) ∧
    (∀pt sfx.
       valid_ptree mmlG pt ∧ ptree_head pt = C ∧
       ptree_fringe pt = MAP TOK master ⇒
       peg_eval mmlPEG (master ++ sfx, sym2peg C) (SOME(sfx,[pt])))
 ⇒
    ∀pfx pt sfx.
      IS_SUFFIX master pfx ∧
      valid_ptree mmlG pt ∧ ptree_head pt = NT (mkNT P) ∧
      (sfx ≠ [] ⇒ HD sfx ∉ firstSet mmlG [SEP]) ∧
      ptree_fringe pt = MAP TOK pfx
  ⇒
      peg_eval mmlPEG (pfx ++ sfx,
                       peg_linfix (mkNT P) (sym2peg C) (sym2peg SEP))
                      (SOME(sfx,[pt]))``,
  strip_tac >>
  simp[peg_linfix_def, list_case_lemma, peg_eval_rpt] >> dsimp[] >>
  gen_tac >>
  completeInduct_on `LENGTH pfx` >> rpt strip_tac >>
  full_simp_tac (srw_ss() ++ DNF_ss) [] >> rveq >>
  `∃subs. pt = Nd (mkNT P) subs`
    by (Cases_on `pt` >> fs[MAP_EQ_CONS] >> rw[] >> fs[]) >> rw[] >> fs[] >>
  Q.UNDISCH_THEN `MAP ptree_head subs ∈ mmlG.rules ' (mkNT P)` mp_tac >>
  simp[MAP_EQ_CONS] >> reverse (rpt strip_tac) >> rveq >> fs[]
  >- (asm_match `ptree_fringe cpt = MAP TK pfx` >>
      map_every qexists_tac [`sfx`, `[cpt]`, `[]`] >>
      first_x_assum (kall_tac o assert (is_forall o concl)) >>
      conj_tac
      >- (fs[rich_listTheory.IS_SUFFIX_compute] >>
          IMP_RES_THEN (assume_tac o SIMP_RULE (srw_ss()) [])
            rich_listTheory.IS_PREFIX_LENGTH >>
          fs[DECIDE ``x:num ≤ y ⇔ x < y ∨ x = y``] >>
          `pfx = master` suffices_by rw[] >>
          metis_tac[rich_listTheory.IS_PREFIX_LENGTH_ANTI, REVERSE_11,
                    listTheory.LENGTH_REVERSE]) >>
      simp[Once pegTheory.peg_eval_cases, mk_linfix_def, peg_eval_seq_NONE] >>
      DISJ1_TAC >>
      Cases_on `SEP` >> fs[sym2peg_def, peg_eval_tok_NONE]
      >- (Cases_on `sfx` >> fs[]) >>
      Cases_on `sfx` >- simp[not_peg0_peg_eval_NIL_NONE, PEG_wellformed] >>
      fs[peg_respects_firstSets]) >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  asm_match `
    mmlG.rules ' (mkNT P) = {[NN P; ptree_head spt; ptree_head cpt];
                             [ptree_head cpt]}
  ` >> asm_match `ptree_head ppt = NN P` >>
  fs[MAP_EQ_APPEND] >> rw[] >>
  asm_match `ptree_fringe ppt = MAP TK pf` >>
  asm_match `ptree_fringe spt = MAP TK sf` >>
  asm_match `ptree_fringe cpt = MAP TK cf` >>
  qispl_then [`mmlG`, `mkNT P`, `ptree_head spt`, `ptree_head cpt`,
              `ppt`, `spt`, `cpt`, `pf`, `sf`, `cf`] mp_tac
    lassoc_reassociated >> simp[MAP_EQ_APPEND] >>
  dsimp[] >>
  map_every qx_gen_tac [`cpt'`, `spt'`, `ppt'`]  >> rpt strip_tac >>
  asm_match `ptree_fringe cpt' = MAP TK cf'` >>
  asm_match `ptree_fringe spt' = MAP TK sf'` >>
  asm_match `ptree_fringe ppt' = MAP TK pf'` >>
  map_every qexists_tac [`sf' ++ pf' ++ sfx`, `[cpt']`] >>
  `0 < LENGTH (MAP TK sf') ∧ 0 < LENGTH (MAP TK cf')`
    by metis_tac [fringe_length_not_nullable] >>
  ntac 2 (pop_assum mp_tac) >> simp[] >> ntac 2 strip_tac >>
  CONV_TAC EXISTS_AND_CONV >> conj_tac
  >- (REWRITE_TAC [GSYM APPEND_ASSOC] >>
      first_x_assum match_mp_tac >> simp[] >>
      fs[rich_listTheory.IS_SUFFIX_compute] >>
      IMP_RES_THEN mp_tac rich_listTheory.IS_PREFIX_LENGTH >>
      asimp[]) >>
  first_x_assum (qspecl_then [`pf'`, `ppt'`, `sfx`] mp_tac) >>
  first_assum (SUBST1_TAC o assert (listSyntax.is_append o lhs o concl)) >>
  asimp[] >>
  `IS_SUFFIX master pf'`
    by (first_x_assum (SUBST_ALL_TAC o
                       assert (listSyntax.is_append o lhs o concl)) >>
        fs[rich_listTheory.IS_SUFFIX_compute,
           listTheory.REVERSE_APPEND] >>
        metis_tac[rich_listTheory.IS_PREFIX_APPEND1]) >>
  simp[] >>
  disch_then (qxchl [`pf1`, `cplist`, `sclist`] strip_assume_tac) >>
  first_x_assum (kall_tac o assert (is_forall o concl)) >>
  first_x_assum (qspecl_then [`spt'`, `sf'`, `pf' ++ sfx`] mp_tac o
                 assert (free_in ``spt:mlptree`` o concl)) >>
  simp[] >>
  Q.UNDISCH_THEN `IS_SUFFIX master (pf ++ sf ++ cf)` mp_tac >>
  simp[rich_listTheory.IS_SUFFIX_compute] >>
  disch_then (mp_tac o MATCH_MP rich_listTheory.IS_PREFIX_LENGTH) >>
  asimp[] >> rpt strip_tac >>
  simp[Once pegTheory.peg_eval_cases] >> dsimp[] >> DISJ2_TAC >>
  map_every qexists_tac [`pf1`, `sclist`, `pf' ++ sfx`, `[spt']`,
                         `cplist`] >> simp[] >>
  Cases_on `ptree_head cpt`
  >- (fs[sym2peg_def] >>
      simp[mk_linfix_def, left_insert_mk_linfix, left_insert_def]) >>
  simp[left_insert_mk_linfix] >> fs[sym2peg_def] >>
  first_x_assum (mp_tac o MATCH_MP peg_sound) >> rw[] >>
  simp[mk_linfix_def, left_insert_def]);

val stoppers_def = Define`
  (stoppers nSpecLine = {ValT; DatatypeT; TypeT}) ∧
  (stoppers nVlist1 = {}) ∧
  (stoppers nV = UNIV) ∧
  (stoppers nTyVarList = {RparT}) ∧
  (stoppers nTypeList2 = UNIV DIFF {CommaT; ArrowT}) ∧
  (stoppers nTypeList1 = UNIV DIFF {CommaT; ArrowT}) ∧
  (stoppers nTypeDec = UNIV DELETE AndT) ∧
  (stoppers nType = UNIV DELETE ArrowT) ∧
  (stoppers nTopLevelDecs = UNIV DIFF {StructureT; ValT; FunT; DatatypeT}) ∧
  (stoppers _ = UNIV)
`;
val _ = export_rewrites ["stoppers_def"]

(*
val completeness = store_thm(
  "completeness",
  ``∀pt N pfx sfx.
      valid_ptree mmlG pt ∧ ptree_head pt = NT (mkNT N) ∧
      (sfx ≠ [] ⇒ HD sfx ∈ stoppers N) ∧ ptree_fringe pt = MAP TOK pfx ⇒
      peg_eval mmlPEG (pfx ++ sfx, nt (mkNT N) I)
                      (SOME(sfx, [pt]))``,
  ho_match_mp_tac parsing_ind >> qx_gen_tac `pt` >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ DNF_ss) []) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss() ++ CONJ_ss) [AND_IMP_INTRO]) >>
  map_every qx_gen_tac [`N`, `pfx`, `sfx`] >> strip_tac >> fs[] >>
  `∃subs. pt = Nd (mkNT N) subs`
    by (Cases_on `pt` >> simp[] >> fs[] >> rw[] >> fs[MAP_EQ_SING]) >>
  rveq >> fs[] >>
  rpt (first_x_assum (mp_tac o assert (free_in ``mmlG.rules`` o concl))) >>
  Cases_on `N` >> simp[cmlG_applied, cmlG_FDOM]
  >- (print_tac "nVlist1" >>
      dsimp[MAP_EQ_CONS] >>
      simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG] >>
      conj_tac
      >- ((* nV nVlist1 *)
          map_every qx_gen_tac [`vpt`, `vlist1pt`] >> strip_tac >>
          rveq >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
          fs[MAP_EQ_APPEND] >>
          asm_match `ptree_fringe vpt = MAP TK vtks` >>
          asm_match `ptree_fringe vlist1pt = MAP TK vltks` >>
          map_every qexists_tac [`[vpt]`, `vltks ++ sfx`, `[vlist1pt]`] >>
          simp[] >> conj_tac
          >- (first_x_assum (qspecl_then [`vpt`, `nV`, `vtks`, `vltks ++ sfx`]
                                         mp_tac o has_length) >>
              simp[] >> disch_then match_mp_tac >>
              erule mp_tac
                (MATCH_MP fringe_length_not_nullable nullable_Vlist1) >>
              simp[]) >>
          first_x_assum (qspecl_then [`vlist1pt`, `nVlist1`, `vltks`, `sfx`]
                                     mp_tac o has_length) >>
          simp[] >> disch_then match_mp_tac >>
          erule mp_tac
            (MATCH_MP fringe_length_not_nullable nullable_V) >> simp[]) >>
      (* nV *)
      qx_gen_tac `vpt` >> strip_tac >>rveq >> fs[] >>
      map_every qexists_tac [`[vpt]`, `sfx`, `[]`] >> simp[] >>
      first_x_assum (qspecl_then [`vpt`, `nV`, `pfx`, `sfx`] mp_tac) >>
      simp[NT_rank_def] >>
      qxchl [`r`] strip_assume_tac
        (MATCH_MP mmlPEG_total nVlist1_expr |> Q.SPEC `[]`) >>
      Cases_on `r` >> simp[] >> Cases_on `x` >> simp[] >>
      imp_res_tac (MATCH_MP (GEN_ALL not_peg0_LENGTH_decreases) peg0_nVlist1) >>
      fs[])
  >- (print_tac "nV" >>
      simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG, peg_V_def,
           peg_eval_choice, gramTheory.assert_def, peg_eval_tok_NONE] >>
      dsimp[MAP_EQ_SING] >> rpt strip_tac >> rveq >>
      fs[MAP_EQ_SING, sumID_def])
  >- (print_tac "nUQTyOp" >>
      simp[MAP_EQ_SING] >> simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG,
           peg_eval_choice, gramTheory.assert_def, peg_eval_tok_NONE] >>
      strip_tac >> rveq >> fs[MAP_EQ_SING])
  >- (print_tac "nUQConstructorName" >>
      simp[MAP_EQ_SING, peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG, peg_UQConstructorName_def,
           gramTheory.assert_def] >>
      strip_tac >> rveq >> fs[MAP_EQ_SING])
  >- (print_tac "nTyvarN" >> dsimp[MAP_EQ_SING] >> simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG] >> rpt strip_tac >>
      fs[MAP_EQ_SING])
  >- (print_tac "nTypeName" >>
      simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG] >>
      rpt strip_tac >> rveq >> fs[]
      >- (DISJ1_TAC >> fs[MAP_EQ_SING] >> rveq >>
          asm_match `NN nUQTyOp = ptree_head pt` >>
          first_x_assum (qspecl_then [`pt`, `nUQTyOp`, `pfx`, `sfx`] mp_tac)>>
          simp[NT_rank_def] >> fs[])
      >- (DISJ2_TAC >> fs[MAP_EQ_CONS] >> simp[peg_eval_seq_NONE] >> rveq >>
          fs[] >>
          asm_match `ptree_head tyvl_pt = NN nTyVarList` >>
          asm_match `ptree_head tyop_pt = NN nUQTyOp` >>
          fs [MAP_EQ_APPEND, MAP_EQ_SING, MAP_EQ_CONS] >> rveq >>
          asm_match `ptree_fringe tyop_pt = MAP TK opf` >> conj_tac
          >- simp[Once pegTheory.peg_eval_cases, FDOM_cmlPEG, mmlpeg_rules_applied,
                  peg_eval_tok_NONE] >>
          dsimp[] >>
          map_every qexists_tac [`[tyvl_pt]`, `opf ++ sfx`, `[tyop_pt]`] >>
          simp[] >>
          asm_match `ptree_fringe tyvl_pt = MAP TK vlf` >>
          first_x_assum
             (qspecl_then [`tyvl_pt`, `nTyVarList`, `vlf`,
                           `RparT::(opf ++ sfx)`] mp_tac o has_length) >>
              simp[] >> metis_tac[listTheory.APPEND_ASSOC, listTheory.APPEND])>>
      DISJ2_TAC >> fs[MAP_EQ_CONS] >> rveq >> fs[MAP_EQ_CONS] >> rveq >>
      simp[peg_eval_seq_NONE, peg_eval_tok_NONE] >>
      simp[Once pegTheory.peg_eval_cases, FDOM_cmlPEG, mmlpeg_rules_applied,
           peg_eval_tok_NONE])
  >- (print_tac "nTypeList2" >> dsimp[MAP_EQ_CONS] >>
      map_every qx_gen_tac [`typt`, `tylpt`] >> rw[] >>
      fs[MAP_EQ_APPEND, MAP_EQ_CONS] >> rw[] >>
      simp[peg_eval_NT_SOME] >> simp[mmlpeg_rules_applied, FDOM_cmlPEG] >>
      dsimp[] >> asm_match `ptree_fringe typt = MAP TK tyf` >>
      asm_match `MAP TK lf = ptree_fringe tylpt` >>
      first_assum (qspecl_then [`typt`, `nType`, `tyf`, `CommaT::lf ++ sfx`]
                               mp_tac o has_length) >>
      simp_tac (srw_ss() ++ ARITH_ss) [] >> simp[] >> strip_tac >>
      map_every qexists_tac [`[typt]`, `lf ++ sfx`, `[tylpt]`] >>
      simp[])
  >- (print_tac "nTypeList1" >> dsimp[MAP_EQ_CONS] >>
      simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG, peg_eval_tok_NONE] >>
      dsimp[] >> conj_tac
      >- (qx_gen_tac `typt` >> rw[] >> fs[] >> DISJ2_TAC >> DISJ1_TAC >>
          first_x_assum (qspecl_then [`typt`, `nType`, `pfx`, `sfx`] mp_tac) >>
          simp[NT_rank_def] >> Cases_on `sfx` >> fs[]) >>
      map_every qx_gen_tac [`typt`, `tylpt`] >> rw[] >>
      fs[MAP_EQ_APPEND, MAP_EQ_CONS] >> rw[] >> DISJ1_TAC >>
      asm_match `ptree_fringe typt = MAP TK tyf` >>
      asm_match `MAP TK tylf = ptree_fringe tylpt` >>
      map_every qexists_tac [`[typt]`, `tylf ++ sfx`, `[tylpt]`] >>
      simp[] >> REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >>
      simp[])
  >- (print_tac "nTypeDec" >> dsimp[MAP_EQ_CONS] >> qx_gen_tac `dtspt` >>
      rw[] >> fs[DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_CONS] >> rw[] >>
      simp[peg_eval_NT_SOME] >>
      simp[FDOM_cmlPEG, mmlpeg_rules_applied, peg_TypeDec_def] >>
      asm_match `MAP TK pfx = ptree_fringe dtspt` >>
      match_mp_tac
        (peg_linfix_complete
          |> Q.INST [`SEP` |-> `TK AndT`, `C` |-> `NN nDtypeDecl`,
                     `P` |-> `nDtypeDecls`, `master` |-> `pfx`]
          |> SIMP_RULE (srw_ss() ++ DNF_ss) [sym2peg_def, MAP_EQ_CONS,
                                             cmlG_applied, EXTENSION,
                                             DISJ_COMM, AND_IMP_INTRO]) >>
      simp[])
  >- (print_tac "nType" >> dsimp[MAP_EQ_CONS] >> conj_tac
      >- (simp[peg_eval_NT_SOME] >>
          simp[mmlpeg_rules_applied, FDOM_cmlPEG, peg_Type_def,
               peg_eval_choice, sumID_def, peg_eval_seq_NONE,
               peg_eval_tok_NONE] >> dsimp[list_case_lemma] >>
          qx_gen_tac `dpt` >> strip_tac >> DISJ1_TAC >> rveq >> fs[] >>
          Cases_on `sfx` >> fs[]
          >- (first_x_assum (qspecl_then [`dpt`, `nDType`, `pfx`, `[]`]
                                         mp_tac) >> simp[NT_rank_def]) >>
          first_x_assum match_mp_tac >> simp[NT_rank_def]) >>
      map_every qx_gen_tac [`dpt`, `typt`] >> rw[] >>
      fs[DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_APPEND, MAP_EQ_CONS] >> rw[] >>
      simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG, peg_Type_def] >>
      asm_match `ptree_fringe dpt = MAP TK df` >>
      asm_match `MAP TK tf = ptree_fringe typt` >> loseC ``NT_rank`` >>
      map_every qexists_tac [`ArrowT::tf ++ sfx`, `[dpt]`,
                             `[Lf (TK ArrowT); typt]`] >> simp[] >>
      REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >> asimp[] >>
      dsimp[peg_eval_choice, sumID_def] >> asimp[])
  >- (print_tac "nTyVarList" >> simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG] >>
      disch_then assume_tac >>
      match_mp_tac (peg_linfix_complete
                      |> Q.INST [`C` |-> `NN nTyvarN`, `SEP` |-> `TK CommaT`,
                                 `P` |-> `nTyVarList`,
                                 `master` |-> `pfx`]
                      |> SIMP_RULE (srw_ss() ++ DNF_ss)
                             [sym2peg_def, cmlG_applied, cmlG_FDOM, EXTENSION,
                              DISJ_COMM, AND_IMP_INTRO]) >>
      simp[MAP_EQ_SING] >> simp[cmlG_FDOM, cmlG_applied] >>
      `NT_rank (mkNT nTyvarN) < NT_rank (mkNT nTyVarList)`
        by simp[NT_rank_def]>> simp[] >> fs[])
  >- (print_tac "nTyOp" >>
      simp[peg_eval_NT_SOME, mmlpeg_rules_applied, FDOM_cmlPEG, MAP_EQ_CONS] >>
      rw[] >> fs[MAP_EQ_CONS]
      >- (asm_match `ptree_head pt = NN nUQTyOp` >>
          first_x_assum (qspecl_then [`pt`, `nUQTyOp`, `pfx`, `sfx`] mp_tac) >>
          simp[NT_rank_def, peg_eval_NT_SOME, mmlpeg_rules_applied,
               FDOM_cmlPEG]) >>
      match_mp_tac peg_respects_firstSets >> simp[firstSet_nUQTyOp, PEG_exprs])
  >- (print_tac "nTopLevelDecs" >> dsimp[MAP_EQ_CONS] >> conj_tac
      >- (simp[peg_eval_NT_SOME] >>
          simp[mmlpeg_rules_applied, FDOM_cmlPEG, peg_eval_rpt] >>
          map_every qx_gen_tac [`tldpt`, `tldspt`] >> rw[] >>
          fs[MAP_EQ_CONS, MAP_EQ_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >> rw[] >>
          asm_match `ptree_fringe tldpt = MAP TK df` >>
          asm_match `ptree_fringe tldspt = MAP TK sf` >>
          Cases_on `sf = []`
          >- (first_x_assum (qspecl_then [`tldpt`, `nTopLevelDec`, `df`, `sfx`]
                                         mp_tac) >>
              simp[NT_rank_def] >> strip_tac >> qexists_tac `[[tldpt]]` >>
              simp[] >> reverse conj_tac
              >- (Cases_on `tldspt` >> fs[cmlG_applied, cmlG_FDOM, MAP_EQ_CONS] >>
                  rw[] >> fs[] >>
                  Q.UNDISCH_THEN `ptree_head tldpt = NN nTopLevelDec` kall_tac >>
                  asm_match `ptree_head tldpt' = NN nTopLevelDec` >>
                  `0 < LENGTH (ptree_fringe tldpt')` suffices_by simp[] >>
                  match_mp_tac (SIMP_RULE (srw_ss() ++ DNF_ss) [AND_IMP_INTRO]
                                          fringe_length_not_nullable) >>
                  qexists_tac `mmlG` >> simp[]) >>
              simp[Once pegTheory.peg_eval_cases] >> qexists_tac `sfx` >> simp[] >>
              simp[Once pegTheory.peg_eval_cases] >>
              reverse (Cases_on `sfx`)
              >- (match_mp_tac peg_respects_firstSets >> fs[PEG_exprs]) >>
              simp[not_peg0_peg_eval_NIL_NONE, PEG_exprs, PEG_wellformed]) >>
          loseC ``NT_rank`` >>
          `¬nullable mmlG [NN nTopLevelDec]` by simp[] >>
          `0 < LENGTH (MAP TK df)`
            by metis_tac [fringe_length_not_nullable] >> fs[] >>
          `0 < LENGTH sf` by (Cases_on `sf` >> fs[]) >>
          `peg_eval mmlPEG (df ++ (sf ++ sfx), nt (mkNT nTopLevelDec) I)
                           (SOME (sf ++ sfx, [tldpt]))` by simp[] >>
          `peg_eval mmlPEG (sf ++ sfx, nt (mkNT nTopLevelDecs) I)
                           (SOME (sfx, [tldspt]))` by asimp[] >>
          pop_assum (qxchl [`tds`] strip_assume_tac o
                     SIMP_RULE (srw_ss()) [mmlpeg_rules_applied, FDOM_cmlPEG,
                                           peg_eval_rpt] o
                     SIMP_RULE (srw_ss()) [peg_eval_NT_SOME]) >>
          simp[Once pegTheory.peg_eval_cases] >> dsimp[] >>
          map_every qexists_tac [`sf ++ sfx`, `[tldpt]`] >> simp[] >>
          fs[] >> qexists_tac `tds` >> simp[]) >>
      rw[] >> fs[] >> rw[] >> simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG, peg_eval_rpt] >>
      qexists_tac `[]` >> simp[] >> simp[Once pegTheory.peg_eval_cases] >>
      Cases_on `sfx` >>
      fs[peg_respects_firstSets, not_peg0_peg_eval_NIL_NONE, PEG_exprs,
         PEG_wellformed])
  >- (print_tac "nTopLevelDec" >> simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG] >> strip_tac >>
      fs[MAP_EQ_SING] >> rw[] >> fs[]
      >- (DISJ1_TAC >> first_x_assum match_mp_tac >> simp[NT_rank_def]) >>
      DISJ2_TAC >> reverse conj_tac
      >- (first_x_assum match_mp_tac >> simp[NT_rank_def]) >>
      `0 < LENGTH (MAP TK pfx)`
        by metis_tac [fringe_length_not_nullable, nullable_Decl] >> fs[] >>
      Cases_on `pfx` >> fs[] >>
      match_mp_tac peg_respects_firstSets >>
      simp[PEG_exprs] >> strip_tac >> rw[] >>
      `StructureT ∈ firstSet mmlG [NN nDecl]`
        by metis_tac [firstSet_nonempty_fringe] >> fs[])
  >- (print_tac "nStructure" >> dsimp[MAP_EQ_CONS] >> rw[] >>
      fs[DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_CONS, MAP_EQ_APPEND] >>
      rw[] >> fs[] >>
      simp[peg_eval_NT_SOME] >> simp[mmlpeg_rules_applied, FDOM_cmlPEG] >>
      dsimp[] >> loseC ``NT_rank`` >>
      asm_match `ptree_head vpt = NN nV` >>
      asm_match `ptree_fringe vpt = MAP TK vf` >>
      asm_match `ptree_head sigpt = NN nOptionalSignatureAscription` >>
      asm_match `ptree_fringe sigpt = MAP TK sf` >>
      asm_match `ptree_head dpt = NN nDecls` >>
      asm_match `ptree_fringe dpt = MAP TK df` >>
      map_every qexists_tac
        [`[vpt]`, `sf ++ [EqualsT; StructT] ++ df ++ [EndT] ++ sfx`,
         `[sigpt]`, `df ++ [EndT] ++ sfx`, `[dpt]`] >>
      simp[] >> REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >>
      asimp[])
  >- (print_tac "nStarTypesP" >> simp[MAP_EQ_CONS] >> rw[] >>
      fs[DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_CONS, MAP_EQ_APPEND] >>
      rw[]
      >- (simp[peg_eval_NT_SOME] >>
          simp[mmlpeg_rules_applied, FDOM_cmlPEG] >> DISJ1_TAC >>
          loseC ``NT_rank`` >>
          REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >> asimp[]) >>
      simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG] >>





*)
val _ = export_theory();
