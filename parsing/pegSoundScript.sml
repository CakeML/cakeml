open HolKernel Parse boolLib bossLib;

open pred_setTheory
open mmlPEGTheory gramTheory gramPropsTheory
open lcsymtacs boolSimps
open parsingPreamble

val _ = new_theory "pegSound";

val d = let
  val d0 = TypeBase.distinct_of ``:(α,β,γ)pegsym``
in
  CONJ d0 (GSYM d0)
end
val i = TypeBase.one_one_of ``:(α,β,γ)pegsym``

val peg_eval_seq_SOME = store_thm(
  "peg_eval_seq_SOME",
  ``peg_eval G (i0, seq s1 s2 f) (SOME (i,r)) ⇔
    ∃i1 r1 r2. peg_eval G (i0, s1) (SOME (i1,r1)) ∧
               peg_eval G (i1, s2) (SOME (i,r2)) ∧ (r = f r1 r2)``,
  simp[Once pegTheory.peg_eval_cases] >> metis_tac[]);

val peg_eval_seq_NONE = store_thm(
  "peg_eval_seq_NONE",
  ``peg_eval G (i0, seq s1 s2 f) NONE ⇔
      peg_eval G (i0, s1) NONE ∨
      ∃i r. peg_eval G (i0,s1) (SOME(i,r)) ∧
            peg_eval G (i,s2) NONE``,
  simp[Once pegTheory.peg_eval_cases] >> metis_tac[]);


val peg_eval_tok_SOME = store_thm(
  "peg_eval_tok_SOME",
  ``peg_eval G (i0, tok P f) (SOME (i,r)) ⇔ ∃h. P h ∧ i0 = h::i ∧ r = f h``,
  simp[Once pegTheory.peg_eval_cases] >> metis_tac[]);

val peg_eval_empty = Store_thm(
  "peg_eval_empty",
  ``peg_eval G (i, empty r) x ⇔ (x = SOME(i,r))``,
  simp[Once pegTheory.peg_eval_cases])

val peg_eval_NT_SOME = store_thm(
  "peg_eval_NT_SOME",
  ``peg_eval G (i0,nt N f) (SOME(i,r)) ⇔
      ∃r0. r = f r0 ∧ N ∈ FDOM G.rules ∧
           peg_eval G (i0,G.rules ' N) (SOME(i,r0))``,
  simp[Once pegTheory.peg_eval_cases]);

val peg_eval_choice = store_thm(
  "peg_eval_choice",
  ``∀x.
     peg_eval G (i0, choice s1 s2 f) x ⇔
      (∃i r. peg_eval G (i0, s1) (SOME(i, r)) ∧ x = SOME(i, f (INL r))) ∨
      (∃i r. peg_eval G (i0, s1) NONE ∧
             peg_eval G (i0, s2) (SOME(i, r)) ∧ x = SOME(i, f (INR r))) ∨
      peg_eval G (i0, s1) NONE ∧ peg_eval G (i0,s2) NONE ∧ (x = NONE)``,
  simp[Once pegTheory.peg_eval_cases, SimpLHS] >>
  simp[optionTheory.FORALL_OPTION, pairTheory.FORALL_PROD] >> metis_tac[]);

val peg_eval_choicel_NIL = Store_thm(
  "peg_eval_choicel_NIL",
  ``peg_eval G (i0, choicel []) x = (x = NONE)``,
  simp[choicel_def, Once pegTheory.peg_eval_cases]);

val peg_eval_choicel_CONS = store_thm(
  "peg_eval_choicel_CONS",
  ``∀x. peg_eval G (i0, choicel (h::t)) x ⇔
          peg_eval G (i0, h) x ∧ x <> NONE ∨
          peg_eval G (i0,h) NONE ∧ peg_eval G (i0, choicel t) x``,
  simp[choicel_def, SimpLHS, Once pegTheory.peg_eval_cases] >>
  simp[sumID_def, pairTheory.FORALL_PROD, optionTheory.FORALL_OPTION]);

val peg_eval_seql_NIL = Store_thm(
  "peg_eval_seql_NIL",
  ``peg_eval G (i0, seql [] f) x ⇔ (x = SOME(i0,f []))``,
  simp[seql_def, pegf_def] >> simp[Once pegTheory.peg_eval_cases]);

val peg_eval_rpt = store_thm(
  "peg_eval_rpt",
  ``peg_eval G (i0, rpt s f) x ⇔
      ∃i l. peg_eval_list G (i0,s) (i,l) ∧ x = SOME(i,f l)``,
  simp[Once pegTheory.peg_eval_cases, SimpLHS] >> metis_tac[]);

val peg_eval_try = store_thm(
  "peg_eval_try",
  ``∀x. peg_eval G (i0, try s) x ⇔
         peg_eval G (i0, s) NONE ∧ x = SOME(i0,[]) ∨
         ∃i r. peg_eval G (i0, s) (SOME(i,r)) ∧ x = SOME(i,r)``,
  simp[Once pegTheory.peg_eval_cases, try_def, SimpLHS, choicel_def,
       peg_eval_choice] >> simp[sumID_def] >> metis_tac[]);

val peg_eval_seql_CONS = store_thm(
  "peg_eval_seql_CONS",
  ``∀x. peg_eval G (i0, seql (h::t) f) x ⇔
          peg_eval G (i0, h) NONE ∧ x = NONE ∨
          (∃rh i1. peg_eval G (i0,h) (SOME(i1,rh)) ∧
                   peg_eval G (i1, seql t I) NONE ∧ x = NONE) ∨
          (∃rh i1 i rt. peg_eval G (i0, h) (SOME(i1,rh)) ∧
                        peg_eval G (i1, seql t I) (SOME(i,rt)) ∧
                        x = SOME(i,f(rh ++ rt)))``,
  simp[seql_def, pegf_def] >>
  simp[SimpLHS, Once pegTheory.peg_eval_cases] >>
  simp[optionTheory.FORALL_OPTION, pairTheory.FORALL_PROD] >>
  conj_tac
  >- (simp[peg_eval_seq_NONE] >> metis_tac[]) >>
  simp[peg_eval_seq_SOME] >> dsimp[] >> metis_tac[]);

val not_peg0_LENGTH_decreases = store_thm(
  "not_peg0_LENGTH_decreases",
  ``¬peg0 G s ⇒ peg_eval G (i0, s) (SOME(i,r)) ⇒ LENGTH i < LENGTH i0``,
  metis_tac[pegTheory.peg_eval_suffix', pegTheory.lemma4_1a])

val peg_eval_TypeDec_wrongtok = store_thm(
  "peg_eval_TypeDec_wrongtok",
  ``tk ≠ DatatypeT ⇒ ¬peg_eval mmlPEG (tk::i, nt (mkNT nTypeDec) f) (SOME x)``,
  simp[Once pegTheory.peg_eval_cases, mmlpeg_rules_applied, FDOM_cmlPEG,
       peg_TypeDec_def, peg_eval_seq_SOME, tokeq_def, peg_eval_tok_SOME]);

val peg_eval_LetDec_wrongtok = store_thm(
  "peg_eval_LetDec_wrongtok",
  ``¬peg_eval mmlPEG (SemicolonT::i, nt (mkNT nLetDec) f) (SOME x)``,
  simp[Once pegTheory.peg_eval_cases, mmlpeg_rules_applied, FDOM_cmlPEG,
       peg_TypeDec_def, peg_eval_seq_SOME, tokeq_def, peg_eval_tok_SOME,
       peg_eval_choicel_CONS, peg_eval_seql_CONS]);

val peg_eval_rpt_never_NONE = store_thm(
  "peg_eval_rpt_never_NONE",
  ``¬peg_eval G (i, rpt sym f) NONE``,
  simp[Once pegTheory.peg_eval_cases]);
val _ = export_rewrites ["peg_eval_rpt_never_NONE"]

val pegsym_to_sym_def = Define`
  (pegsym_to_sym (tok P f) = if f = mktokLf then { TK t | P t } else ∅) ∧
  pegsym_to_sym (nt N f) = { NT N } ∧
  pegsym_to_sym _ = {}
`

val peg_linfix_correct_lemma = store_thm(
  "peg_linfix_correct_lemma",
  ``∀UpperN sym sepsym i0 i pts.
      peg_eval mmlPEG (i0, peg_linfix UpperN sym sepsym) (SOME(i,pts)) ⇒
      (∀i0' i pts s.
         s ∈ {sym;sepsym} ⇒
         LENGTH i0' < LENGTH i0 ⇒
         peg_eval mmlPEG (i0',s) (SOME(i,pts)) ⇒
         ∃pt. pts = [pt] ∧ ptree_head pt ∈ pegsym_to_sym s ∧
              valid_ptree mmlG pt ∧ MAP TK i0' = ptree_fringe pt ++ MAP TK i) ∧
      (∀i pts s.
         s ∈ {sym; sepsym} ⇒
         peg_eval mmlPEG (i0, s) (SOME(i,pts)) ⇒
         ∃pt. pts = [pt] ∧ ptree_head pt ∈ pegsym_to_sym s ∧
              valid_ptree mmlG pt ∧ MAP TK i0 = ptree_fringe pt ++ MAP TK i) ∧
      ¬peg0 mmlPEG sym ∧
      UpperN ∈ FDOM mmlG.rules ∧
      {[gsym] | gsym ∈ pegsym_to_sym sym } ⊆ mmlG.rules ' UpperN ∧
      {[NT UpperN; gsep; gsym] |
          gsep ∈ pegsym_to_sym sepsym ∧ gsym ∈ pegsym_to_sym sym } ⊆
        mmlG.rules ' UpperN ⇒
      ∃pt. pts = [pt] ∧ ptree_head pt = NT UpperN ∧ valid_ptree mmlG pt ∧
           MAP TK i0 = ptree_fringe pt ++ MAP TK i``,
  rpt strip_tac >> qpat_assum `peg_eval X Y Z` mp_tac >>
  simp[peg_linfix_def, peg_eval_rpt, peg_eval_seq_SOME] >>
  rpt strip_tac >> rveq >>
  asm_match `peg_eval mmlPEG (i0, sym) (SOME(i1,r1))` >>
  first_assum (qspecl_then [`i1`, `r1`, `sym`] mp_tac) >> simp_tac(srw_ss())[]>>
  ASM_REWRITE_TAC[] >> disch_then (qxchl[`rpt1`] strip_assume_tac) >> simp[] >>
  rveq >>
  qpat_assum `peg_eval_list X Y Z` mp_tac >>
  `∃i2. i2 = i1 ∧ LENGTH i2 ≤ LENGTH i1` by simp[] >>
  Q.UNDISCH_THEN `i2 = i1` (SUBST1_TAC o SYM) >>
  `∃acc. MAP ptree_head acc ∈ mmlG.rules ' UpperN ∧
         (∀pt. MEM pt acc ⇒ valid_ptree mmlG pt) ∧
         [rpt1] = acc ∧ ptree_fringe rpt1 = FLAT (MAP ptree_fringe acc)`
    by (simp[] >> fs[SUBSET_DEF]) >>
  ntac 2 (pop_assum SUBST1_TAC) >> ntac 2 (pop_assum mp_tac) >>
  pop_assum mp_tac >> simp[AND_IMP_INTRO, GSYM CONJ_ASSOC] >>
  map_every qid_spec_tac [`acc`, `i2`,`i`, `l`] >>
  Induct >- simp[Once pegTheory.peg_eval_cases, mk_linfix_def] >>
  simp[Once pegTheory.peg_eval_cases] >>
  simp[peg_eval_seq_SOME, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
       GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_FORALL_IMP_THM] >>
  map_every qx_gen_tac [`i`, `i1'`, `acc`, `i3'`, `i2'`, `sep_r`, `sym_r`] >>
  strip_tac >>
  `LENGTH i1 < LENGTH i0` by metis_tac[not_peg0_LENGTH_decreases] >>
  `LENGTH i1' < LENGTH i0` by decide_tac >>
  first_assum (qspecl_then [`i1'`, `i2'`, `sep_r`, `sepsym`] mp_tac) >>
  rpt kill_asm_guard >>
  disch_then (qxchl [`sep_pt`] strip_assume_tac) >> rveq >>
  `LENGTH i2' ≤ LENGTH i1'`
    by metis_tac[pegTheory.peg_eval_suffix',
                 DECIDE``x:num ≤ y ⇔ x = y ∨ x < y``] >>
  `LENGTH i2' < LENGTH i0` by decide_tac >>
  first_x_assum (qspecl_then [`i2'`, `i3'`, `sym_r`, `sym`] mp_tac) >>
  rpt kill_asm_guard >>
  disch_then (qxchl [`sym_pt`] strip_assume_tac) >> rveq >>
  simp[mk_linfix_def] >>
  `LENGTH i3' < LENGTH i2'` by metis_tac[not_peg0_LENGTH_decreases] >>
  `LENGTH i3' ≤ LENGTH i1` by decide_tac >>
  first_x_assum (qspecl_then [`i`, `i3'`, `[Nd UpperN acc; sep_pt; sym_pt]`]
                             mp_tac) >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  `[NT UpperN; ptree_head sep_pt; ptree_head sym_pt] ∈ mmlG.rules ' UpperN`
    by fs[SUBSET_DEF] >>
  simp[]);

val length_no_greater = store_thm(
  "length_no_greater",
  ``peg_eval G (i0, sym) (SOME(i,r)) ⇒ LENGTH i ≤ LENGTH i0``,
  metis_tac[pegTheory.peg_eval_suffix',
            DECIDE ``x ≤ y:num ⇔ x < y ∨ x = y``]);

val _ = augment_srw_ss [rewrites [
  peg_eval_seql_CONS, peg_eval_tok_SOME, tokeq_def, bindNT_def, mktokLf_def,
  peg_eval_choicel_CONS, pegf_def, peg_eval_seq_SOME, pnt_def, peg_eval_try,
  try_def]]

val peg_eval_nTyOp_wrongtok = store_thm(
  "peg_eval_nTyOp_wrongtok",
  ``¬peg_eval mmlPEG (LparT::i, nt (mkNT nTyOp) f) (SOME x)``,
  simp[Once pegTheory.peg_eval_cases, mmlpeg_rules_applied, FDOM_cmlPEG] >>
  simp[Once pegTheory.peg_eval_cases, mmlpeg_rules_applied, FDOM_cmlPEG]);

val peg_sound = store_thm(
  "peg_sound",
  ``∀N i0 i pts.
       peg_eval mmlPEG (i0,nt N I) (SOME(i,pts)) ⇒
       ∃pt. pts = [pt] ∧ ptree_head pt = NT N ∧
            valid_ptree mmlG pt ∧
            MAP TOK i0 = ptree_fringe pt ++ MAP TOK i``,
  ntac 2 gen_tac >> `?iN. iN = (i0,N)` by simp[] >> pop_assum mp_tac >>
  map_every qid_spec_tac [`i0`, `N`, `iN`] >>
  qispl_then [`measure (LENGTH:token list->num) LEX measure NT_rank`]
             (ho_match_mp_tac o
              SIMP_RULE (srw_ss()) [pairTheory.WF_LEX,
                                    prim_recTheory.WF_measure])
             relationTheory.WF_INDUCTION_THM >>
  dsimp[pairTheory.LEX_DEF] >>
  map_every qx_gen_tac [`N`, `i0`, `i`, `pts`] >> strip_tac >>
  simp[peg_eval_NT_SOME, mmlPEGTheory.FDOM_cmlPEG] >>
  disch_then (CONJUNCTS_THEN2 strip_assume_tac mp_tac) >> rveq >>
  simp[mmlPEGTheory.mmlpeg_rules_applied]
  >- (print_tac "nREPLTop">>
      `NT_rank (mkNT nE) < NT_rank (mkNT nREPLTop) ∧
       NT_rank (mkNT nTopLevelDec) < NT_rank (mkNT nREPLTop)`
          by simp[NT_rank_def] >>
      strip_tac >> rveq >> simp[] >>
      first_x_assum (erule strip_assume_tac) >> rveq >>
      dsimp[cmlG_applied, cmlG_FDOM])
  >- (print_tac "nREPLPhrase" >>
      `NT_rank (mkNT nE) < NT_rank (mkNT nREPLPhrase) ∧
       NT_rank (mkNT nTopLevelDecs) < NT_rank (mkNT nREPLPhrase)`
          by simp[NT_rank_def] >>
      strip_tac >> rveq >> simp[] >>
      first_x_assum (erule strip_assume_tac) >> rveq >>
      dsimp[cmlG_applied, cmlG_FDOM])
  >- (print_tac "nTopLevelDecs" >>
      qmatch_abbrev_tac `peg_eval mmlPEG (i0, rpt NNN FF) (SOME(i,pts)) ⇒ QQ`>>
      map_every markerLib.UNABBREV_TAC ["NNN", "QQ"] >>
      `(FF [] = [Nd (mkNT nTopLevelDecs) []]) ∧
       ∀h t. FF ([h]::t) = [Nd (mkNT nTopLevelDecs) [h; HD (FF t)]]`
        by simp[Abbr`FF`] >>
      markerLib.RM_ABBREV_TAC "FF" >> simp[peg_eval_rpt] >>
      disch_then (qxchl [`tds`] mp_tac) >>
      Q.SUBGOAL_THEN
        `∃ii. ii = i0 ∧ (LENGTH ii < LENGTH i0 \/ ii = i0)`
        (qxchl [`ii`] (CONJUNCTS_THEN assume_tac)) >- simp[] >>
      Q.UNDISCH_THEN `ii = i0` (SUBST1_TAC o SYM) >>
      pop_assum mp_tac >>
      map_every qid_spec_tac [`ii`, `i`, `pts`, `tds`] >> simp[] >>
      Induct_on `tds`
      >- simp[Once pegTheory.peg_eval_cases, cmlG_applied, cmlG_FDOM] >>
      map_every qx_gen_tac [`h`, `i`, `ii`] >> strip_tac >>
      simp[Once pegTheory.peg_eval_cases] >>
      disch_then (qxchl [`i1`] strip_assume_tac) >| [
        ALL_TAC,
        `NT_rank (mkNT nTopLevelDec) < NT_rank (mkNT nTopLevelDecs)`
          by simp[NT_rank_def]
      ] >>
      first_x_assum (erule mp_tac) >>
      `LENGTH i1 < LENGTH ii`
        by metis_tac[peg0_nTopLevelDec, not_peg0_LENGTH_decreases] >> rveq >>
      `LENGTH i1 < LENGTH i0` by decide_tac >>
      fs[DISJ_IMP_THM, FORALL_AND_THM] >>
      first_x_assum (erule mp_tac) >>
      disch_then (qxchl [`ds_pt`] strip_assume_tac) >>
      disch_then (qxchl [`d_pt`] strip_assume_tac) >> simp[] >>
      dsimp[cmlG_applied, cmlG_FDOM])
  >- (print_tac "nTopLevelDec" >>
      `NT_rank (mkNT nStructure) < NT_rank (mkNT nTopLevelDec) ∧
       NT_rank (mkNT nDecl) < NT_rank (mkNT nTopLevelDec)`
        by simp[NT_rank_def] >>
      strip_tac >>
      first_x_assum (erule mp_tac) >>
      strip_tac >> simp[cmlG_FDOM, cmlG_applied])
  >- (print_tac "nStructure" >> strip_tac >> rveq >>
      simp[DISJ_IMP_THM, FORALL_AND_THM, cmlG_FDOM, cmlG_applied] >>
      loseC ``NT_rank`` >> fs[] >>
      asm_match `peg_eval mmlPEG (vi, nt (mkNT nV) I) (SOME(opti,vt))` >>
      `LENGTH vi < SUC (LENGTH vi)` by decide_tac >>
      first_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      `LENGTH opti < LENGTH vi`
        by metis_tac[not_peg0_LENGTH_decreases, peg0_nV] >>
      `LENGTH opti < SUC (LENGTH vi)` by decide_tac >>
      first_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      asm_match `peg_eval mmlPEG (opti, OPTSIG)
                          (SOME (EqualsT::StructT::di,[opt]))` >>
      `LENGTH (EqualsT::StructT::di) ≤ LENGTH opti`
        by metis_tac[pegTheory.peg_eval_suffix',
                     DECIDE``x:num ≤ y ⇔ x < y ∨ x = y``] >> fs[] >>
      `LENGTH di < SUC (LENGTH vi)` by decide_tac >>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[])
  >- (print_tac "nOptionalSignatureAscription" >> strip_tac >> rveq >>
      simp[cmlG_applied, cmlG_FDOM] >> dsimp[] >>
      loseC ``NT_rank`` >> dsimp[MAP_EQ_SING] >> csimp[] >> fs[] >>
      metis_tac [DECIDE ``x < SUC x``])
  >- (print_tac "nSignatureValue" >>
      strip_tac >> rveq >> simp[cmlG_FDOM, cmlG_applied, MAP_EQ_SING] >>
      dsimp[] >> csimp[] >>
      first_x_assum (fn patth =>
        first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
      dsimp[])
  >- (print_tac "nSpecLineList" >> strip_tac >> simp[cmlG_applied, cmlG_FDOM]
      >- (`NT_rank (mkNT nSpecLine) < NT_rank (mkNT nSpecLineList)`
             by simp[NT_rank_def] >>
          first_x_assum (erule mp_tac) >>
          asm_match
            `peg_eval mmlPEG (i0, nt (mkNT nSpecLine) I) (SOME (i1,r))` >>
          `LENGTH i1 < LENGTH i0`
            by metis_tac[not_peg0_LENGTH_decreases, peg0_nSpecLine] >>
          first_x_assum (erule mp_tac) >> rpt strip_tac >> rveq >> fs[])
      >- (dsimp[MAP_EQ_SING] >> csimp[]>>fs[] >> metis_tac[DECIDE``x < SUC x``])
      >> fs[cmlG_FDOM, cmlG_applied, MAP_EQ_SING] >> dsimp[] >> csimp[] >>
          metis_tac[DECIDE``x< SUC x``])
  >- (print_tac "nSpecLine" >> strip_tac >> rveq >>
      fs[cmlG_applied, cmlG_FDOM, peg_eval_TypeDec_wrongtok]
      >- (asm_match
            `peg_eval mmlPEG (i1, nt (mkNT nV) I) (SOME(ColonT::i2,r))` >>
          `LENGTH i1 < SUC (LENGTH i1)` by DECIDE_TAC >>
          first_assum (erule strip_assume_tac) >>
          `LENGTH (ColonT::i2) < LENGTH i1`
            by metis_tac[not_peg0_LENGTH_decreases, peg0_nV] >> fs[] >>
          `LENGTH i2 < SUC(LENGTH i1)` by decide_tac >>
          first_x_assum (erule strip_assume_tac) >> rveq >> dsimp[])
      >- (dsimp[MAP_EQ_SING] >> csimp[] >> metis_tac[DECIDE``x<SUC x``])>>
      `NT_rank (mkNT nTypeDec) < NT_rank (mkNT nSpecLine)`
         by simp[NT_rank_def] >>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[])
  >- (print_tac "nDecls" >>
      `NT_rank (mkNT nDecl) < NT_rank (mkNT nDecls)`
        by simp[NT_rank_def] >>
      strip_tac >> rveq >> fs[cmlG_applied, cmlG_FDOM]
      >- (first_x_assum (erule strip_assume_tac) >>
          asm_match `peg_eval mmlPEG (i0,nt (mkNT nDecl) I) (SOME(i1,r))` >>
          dsimp[MAP_EQ_SING] >>
          `LENGTH i1 < LENGTH i0`
            by metis_tac[not_peg0_LENGTH_decreases,peg0_nDecl] >>
          first_x_assum (erule strip_assume_tac) >>
          dsimp[MAP_EQ_SING])
      >- (dsimp[MAP_EQ_SING] >> csimp[] >> metis_tac[DECIDE``x<SUC x``]) >>
      dsimp[MAP_EQ_SING] >> csimp[] >> metis_tac[DECIDE``x<SUC x``])
  >- (print_tac "nDecl" >>
      rpt strip_tac >> rveq >> fs[peg_eval_TypeDec_wrongtok]
      >- (asm_match `peg_eval mmlPEG (i1, nt (mkNT nPattern) I)
                              (SOME(EqualsT::i2,r))` >>
          `LENGTH i1 < SUC (LENGTH i1)` by decide_tac >>
          first_assum (erule strip_assume_tac) >> rveq >>
          `LENGTH (EqualsT::i2) ≤ LENGTH i1`
            by metis_tac[pegTheory.peg_eval_suffix',
                         DECIDE``x≤y ⇔ x = y ∨ x < y:num``] >> fs[]>>
          `LENGTH i2 < SUC (LENGTH i1)` by decide_tac >>
          first_x_assum (erule strip_assume_tac) >> rveq >>
          simp[cmlG_FDOM, cmlG_applied, MAP_EQ_SING] >> dsimp[])
      >- (dsimp[cmlG_applied, cmlG_FDOM, MAP_EQ_SING] >> csimp[] >>
          metis_tac[DECIDE ``x<SUC x``]) >>
      `NT_rank (mkNT nTypeDec) < NT_rank (mkNT nDecl)`
        by simp[NT_rank_def] >>
      first_x_assum (erule strip_assume_tac) >>
      dsimp[cmlG_FDOM, cmlG_applied])
  >- (print_tac "nLetDecs" >> rpt strip_tac >> rveq >>
      simp[cmlG_applied, cmlG_FDOM] >> fs[peg_eval_LetDec_wrongtok]
      >- (simp[] >>
          `NT_rank (mkNT nLetDec) < NT_rank (mkNT nLetDecs)`
            by simp[NT_rank_def] >>
          first_x_assum (erule strip_assume_tac) >> rveq >>
          dsimp[cmlG_applied, cmlG_FDOM, MAP_EQ_SING] >> csimp[] >>
          metis_tac[not_peg0_LENGTH_decreases, peg0_nLetDec]) >>
      dsimp[MAP_EQ_SING] >> csimp[] >> metis_tac[DECIDE ``x < SUC x``])
  >- (print_tac "nLetDec" >>
      rpt strip_tac >> rveq >> simp[cmlG_FDOM, cmlG_applied, MAP_EQ_SING] >> fs[]
      >- (dsimp[listTheory.APPEND_EQ_CONS, MAP_EQ_SING] >> csimp[] >>
          asm_match`peg_eval mmlPEG (i1,nt (mkNT nV) I) (SOME(EqualsT::i2,r))` >>
          `LENGTH i1 < SUC (LENGTH i1)` by decide_tac >>
          first_assum (erule strip_assume_tac) >> rveq >> simp[] >>
          `LENGTH (EqualsT::i2) ≤ LENGTH i1`
            by metis_tac[pegTheory.peg_eval_suffix',
                         DECIDE``x≤y ⇔ x = y ∨ x < y:num``] >> fs[]>>
          `LENGTH i2 < SUC (LENGTH i1)` by decide_tac >>
          metis_tac[]) >>
      dsimp[] >> csimp[] >> metis_tac[DECIDE``x<SUC x``])
  >- (print_tac "nPatternList1" >> strip_tac >>
      pop_assum (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[pegsym_to_sym_def] >>
      simp[DISJ_IMP_THM, FORALL_AND_THM, cmlG_applied, cmlG_FDOM, NT_rank_def,
           SUBSET_DEF, EXTENSION, peg_eval_tok_SOME, mktokLf_def,
           pegsym_to_sym_def])
  >- (print_tac "nPatternList2" >>
      strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM] >>
      dsimp[listTheory.APPEND_EQ_CONS, MAP_EQ_SING] >> csimp[] >>
      `NT_rank (mkNT nPattern) < NT_rank (mkNT nPatternList2)`
        by simp[NT_rank_def] >>
      first_x_assum (erule mp_tac) >> strip_tac >> rveq >> simp[] >>
      metis_tac [not_peg0_LENGTH_decreases, peg0_nPattern, listTheory.LENGTH,
                 DECIDE ``SUC x < y ⇒ x < y``])
  >- (print_tac "nPtuple" >>
      strip_tac >> rveq >> fs[cmlG_FDOM, cmlG_applied, MAP_EQ_SING] >>
      dsimp[] >> csimp[] >>
      first_x_assum
        (fn patth => first_assum
             (fn th => mp_tac (PART_MATCH (lhand o rand) patth (concl th)))) >>
      dsimp[])
  >- (print_tac "nPattern" >>
      `NT_rank (mkNT nConstructorName) < NT_rank (mkNT nPattern) ∧
       NT_rank (mkNT nPbase) < NT_rank (mkNT nPattern)`
        by simp[NT_rank_def] >>
      strip_tac >> rveq >> simp[] >>
      first_x_assum (erule strip_assume_tac) >> rveq >>
      dsimp[cmlG_applied, cmlG_FDOM, MAP_EQ_SING] >> csimp[] >>
      metis_tac[not_peg0_LENGTH_decreases, peg0_nConstructorName])
  >- (print_tac "nPbase" >>
      `NT_rank (mkNT nV) < NT_rank (mkNT nPbase) ∧
       NT_rank (mkNT nConstructorName) < NT_rank (mkNT nPbase)`
        by simp[NT_rank_def] >>
      strip_tac >> rveq >> simp[cmlG_FDOM, cmlG_applied, MAP_EQ_SING] >>
      TRY (first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
           NO_TAC) >>
      TRY (dsimp[] >> NO_TAC)
      >- (asm_match `isInt tt` >> Cases_on `tt` >> fs[]) >>
      first_x_assum
        (fn patth => first_assum
             (fn th => mp_tac (PART_MATCH (lhand o rand) patth (concl th)))) >>
      dsimp[])
  >- (print_tac "nConstructorName" >>
      simp[pairTheory.EXISTS_PROD, gramTheory.assert_def] >>
      `NT_rank (mkNT nUQConstructorName) < NT_rank (mkNT nConstructorName)`
        by simp[NT_rank_def] >>
      strip_tac >> rveq >> simp[]
      >- (first_x_assum (erule strip_assume_tac) >> rveq >>
          simp[cmlG_applied, cmlG_FDOM] >> NO_TAC) >>
      simp[cmlG_FDOM, cmlG_applied] >>
      asm_match `destLongidT t = SOME(m,v)` >> Cases_on `t` >> fs[])
  >- (print_tac "nUQConstructorName" >>
      simp[peg_UQConstructorName_def] >>
      disch_then (qxchl [`t`] strip_assume_tac) >> rveq >> simp[] >>
      Cases_on `t` >> fs[gramTheory.assert_def, cmlG_applied, cmlG_FDOM])
  >- (print_tac "nDconstructor" >>
      `NT_rank (mkNT nUQConstructorName) < NT_rank (mkNT nDconstructor)`
        by simp[NT_rank_def] >>
      strip_tac >>
      rveq >> simp[cmlG_FDOM, cmlG_applied, listTheory.APPEND_EQ_CONS,
                   MAP_EQ_SING] >>
      first_x_assum (erule strip_assume_tac) >> simp[] >> rveq >> dsimp[] >>
      csimp[] >>
      first_x_assum
        (fn patth => first_assum
             (fn th => mp_tac (PART_MATCH (lhand o rand) patth (concl th)))) >>
      metis_tac[not_peg0_LENGTH_decreases, peg0_nUQConstructorName,
                listTheory.LENGTH, DECIDE``SUC x < y ⇒ x < y``])
  >- (print_tac "nDtypeDecl" >>
      `NT_rank (mkNT nTypeName) < NT_rank (mkNT nDtypeDecl)`
        by simp[NT_rank_def] >>
      strip_tac >> rveq >>
      dsimp[cmlG_applied, cmlG_FDOM, listTheory.APPEND_EQ_CONS, MAP_EQ_SING] >>
      csimp[] >>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >> csimp[] >>
      `∀x:mlptree.
         NN nDtypeCons = ptree_head x ⇔ ptree_head x = NN nDtypeCons`
        by simp[EQ_SYM_EQ] >>
      pop_assum (fn th => simp[th]) >>
      first_x_assum (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[DISJ_IMP_THM, FORALL_AND_THM, peg_eval_tok_SOME, pegsym_to_sym_def,
           mktokLf_def, cmlG_applied, cmlG_FDOM, SUBSET_DEF] >>
      (peg0_nTypeName |> Q.INST[`f` |-> `I`] |> assume_tac) >>
      erule mp_tac (GEN_ALL not_peg0_LENGTH_decreases)>>
      simp[])
  >- (print_tac "nTypeDec" >> simp[peg_TypeDec_def] >> strip_tac >> rveq >>
      dsimp[cmlG_FDOM, cmlG_applied, mktokLf_def, MAP_EQ_SING] >> csimp[] >>
      fs[] >> pop_assum (mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[pegsym_to_sym_def, cmlG_applied, cmlG_FDOM, SUBSET_DEF,
           DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >> rveq >> simp[])
  >- (print_tac "nTyVarList" >> strip_tac >>
      `NT_rank (mkNT nTyvarN) < NT_rank (mkNT nTyVarList)`
        by simp[NT_rank_def] >>
      first_x_assum (mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[DISJ_IMP_THM, pegsym_to_sym_def, cmlG_FDOM, cmlG_applied,
           SUBSET_DEF, FORALL_AND_THM, mktokLf_def] >> dsimp[])
  >- (print_tac "nTypeName" >>
      simp[] >> strip_tac >> rveq >>
      dsimp[cmlG_FDOM, cmlG_applied, MAP_EQ_SING]
      >- (first_x_assum (fn patth =>
           first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          simp[NT_rank_def] >> strip_tac >> rveq >> dsimp[])
      >- (simp[listTheory.APPEND_EQ_CONS] >> dsimp[MAP_EQ_CONS] >>
          csimp[] >> loseC ``NT_rank`` >>
          first_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nTyVarList``) o concl)) >>
          rpt kill_asm_guard >>
          disch_then (qxchl [`tyvl_pt`] strip_assume_tac) >>
          rveq >> simp[] >>
          first_x_assum (assume_tac o MATCH_MP length_no_greater o
                         assert (free_in ``nTyVarList`` o concl)) >> fs[] >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          rpt kill_asm_guard >> metis_tac[])
      >- (first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          simp[] >> strip_tac >> rveq >> simp[] >> asm_match `isTyvarT HH` >>
          qpat_assum `isTyvarT HH` mp_tac >> Cases_on `HH` >> simp[])
      >- (fs[] >> rveq >> fs[])
      >- (fs[] >> rveq >> fs[]) >>
      fs[] >> rveq >> fs[])
  >- (print_tac "nStarTypesP" >>
      strip_tac >> rveq >>
      dsimp[cmlG_FDOM, cmlG_applied, MAP_EQ_SING] >> csimp[] >>
      first_x_assum (fn patth =>
         first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
      simp[NT_rank_def] >> strip_tac >> rveq >> simp[])
  >- (print_tac "nStarTypes" >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[DISJ_IMP_THM, FORALL_AND_THM, cmlG_applied, cmlG_FDOM,
           pegsym_to_sym_def, SUBSET_DEF] >>
      rpt strip_tac >>
      first_x_assum (fn patth =>
         first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
      simp[NT_rank_def])
  >- (print_tac "nUQTyOp" >> dsimp[cmlG_FDOM, cmlG_applied] >>
      qx_gen_tac `h` >> Cases_on `h` >> simp[])
  >- (print_tac "nTyOp" >> strip_tac >> rveq >>
      dsimp[cmlG_applied, cmlG_FDOM, MAP_EQ_SING]
      >- (first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          simp[NT_rank_def] >> strip_tac >> rveq >> simp[]) >>
      asm_match `isLongidT h` >> Cases_on `h` >> fs[])
  >- (print_tac "nTypeList1" >> strip_tac >> rveq >>
      dsimp[cmlG_FDOM, cmlG_applied, listTheory.APPEND_EQ_CONS, MAP_EQ_SING] >>
      csimp[] >>
      `NT_rank (mkNT nType) < NT_rank (mkNT nTypeList1)` by simp[NT_rank_def]
      >- (first_x_assum (erule mp_tac) >>
          erule assume_tac
                (length_no_greater |> Q.GEN `sym`
                                   |> Q.ISPEC `nt (mkNT nType) I` |> GEN_ALL) >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          fs[] >> asimp[] >> rpt strip_tac >> rveq >> simp[])
      >- (first_x_assum (erule strip_assume_tac) >> rveq >> simp[]) >>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[])
  >- (print_tac "nTypeList2" >> strip_tac >> rveq >>
      dsimp[cmlG_applied, cmlG_FDOM, listTheory.APPEND_EQ_CONS, MAP_EQ_SING]>>
      csimp[] >>
      `NT_rank (mkNT nType) < NT_rank (mkNT nTypeList2)` by simp[NT_rank_def]>>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
      erule assume_tac
            (length_no_greater |> Q.GEN `sym` |> Q.ISPEC `nt (mkNT nType) I`
                               |> GEN_ALL) >> fs[] >> asimp[] >>
      strip_tac >> rveq >> simp[])
  >- (print_tac "nDType" >> strip_tac >> rveq >> simp[]
      >- (qpat_assum `peg_eval mmlPEG (i1, rpt X Y) Z` mp_tac >>
          simp[peg_eval_rpt] >>
          disch_then (qxchl [`tyops`] strip_assume_tac) >> rveq >> simp[] >>
          asm_match `peg_eval_list mmlPEG (i1, nt (mkNT nTyOp) I) (i,tyops)`>>
          pop_assum mp_tac >>
          `∃i2. LENGTH i2 < SUC (LENGTH i1) ∧ i1 = i2` by simp[] >>
          pop_assum SUBST1_TAC >> pop_assum mp_tac >>
          asm_match `isTyvarT tyv` >>
          `∃acc.
             MAP ptree_head acc ∈ mmlG.rules ' (mkNT nDType) ∧
             (∀pt. MEM pt acc ⇒ valid_ptree mmlG pt) ∧
             TK tyv::MAP TK i2 = FLAT (MAP ptree_fringe acc) ++ MAP TK i2 ∧
             [Lf (TK tyv)] = acc`
            by (simp[cmlG_FDOM, cmlG_applied] >> Cases_on `tyv` >> fs[]) >>
          ntac 2 (pop_assum SUBST1_TAC) >> ntac 2 (pop_assum mp_tac) >>
          map_every qid_spec_tac [`acc`, `i2`, `i`, `tyops`] >> Induct
          >- (simp[Once pegTheory.peg_eval_cases] >>
              simp[cmlG_FDOM, cmlG_applied]) >>
          map_every qx_gen_tac [`tyop`, `i`, `i2`, `acc`] >>
          simp[Once pegTheory.peg_eval_cases] >> ntac 3 strip_tac >>
          disch_then (qxchl [`i3`] strip_assume_tac) >>
          fs[] >> first_x_assum (erule mp_tac) >>
          disch_then (qxchl [`tyop_pt`] strip_assume_tac) >> rveq >>
          simp[] >>
          `LENGTH i3 < LENGTH i2`
            by metis_tac[not_peg0_LENGTH_decreases, peg0_nTyOp] >>
          `LENGTH i3 < SUC (LENGTH i1)` by decide_tac >>
          first_x_assum
            (qspecl_then [`i`, `i3`, `[Nd (mkNT nDType) acc; tyop_pt]`]
                         mp_tac)>>
          simp[cmlG_applied, cmlG_FDOM, DISJ_IMP_THM, FORALL_AND_THM])
      >- (`NT_rank (mkNT nTyOp) < NT_rank (mkNT nDType)` by simp[NT_rank_def] >>
          first_x_assum (erule mp_tac) >>
          disch_then (qxchl [`tyop_pt`] strip_assume_tac) >> rveq >> simp[] >>
          qpat_assum `peg_eval mmlPEG XX NONE` (K ALL_TAC) >>
          erule strip_assume_tac
            (MATCH_MP not_peg0_LENGTH_decreases peg0_nTyOp) >>
          qpat_assum `peg_eval mmlPEG (II, rpt XX FF) YY` mp_tac >>
          simp[peg_eval_rpt] >> disch_then (qxchl [`tyops`] strip_assume_tac) >>
          rveq >> simp[] >>
          asm_match `peg_eval_list mmlPEG (i1, nt (mkNT nTyOp) I) (i,tyops)`>>
          pop_assum mp_tac >>
          `∃i2. LENGTH i2 < LENGTH i0 ∧ i1 = i2` by simp[] >>
          pop_assum SUBST1_TAC >> pop_assum mp_tac >>
          `∃acc.
             MAP ptree_head acc ∈ mmlG.rules ' (mkNT nDType) ∧
             (∀pt. MEM pt acc ⇒ valid_ptree mmlG pt) ∧
             ptree_fringe tyop_pt ++ MAP TK i2 =
               FLAT (MAP ptree_fringe acc) ++ MAP TK i2 ∧
             [tyop_pt] = acc`
            by (simp[cmlG_FDOM, cmlG_applied]) >>
          ntac 2 (pop_assum SUBST1_TAC) >> ntac 2 (pop_assum mp_tac) >>
          map_every qid_spec_tac [`acc`, `i2`, `i`, `tyops`] >> Induct
          >- (simp[Once pegTheory.peg_eval_cases] >>
              simp[cmlG_FDOM, cmlG_applied]) >>
          map_every qx_gen_tac [`tyop`, `i`, `i2`, `acc`] >>
          simp[Once pegTheory.peg_eval_cases] >> ntac 3 strip_tac >>
          disch_then (qxchl [`i3`] strip_assume_tac) >>
          first_x_assum (erule mp_tac) >>
          disch_then (qxchl [`tyop_pt2`] strip_assume_tac) >> rveq >>
          simp[] >>
          `LENGTH i3 < LENGTH i2`
            by metis_tac[not_peg0_LENGTH_decreases, peg0_nTyOp] >>
          `LENGTH i3 < LENGTH i0` by decide_tac >>
          first_x_assum
            (qspecl_then [`i`, `i3`, `[Nd (mkNT nDType) acc; tyop_pt2]`]
                         mp_tac)>>
          simp[cmlG_applied, cmlG_FDOM, DISJ_IMP_THM, FORALL_AND_THM])
      >- ((* type in parentheses followed by tyops case *)
          rpt (qpat_assum `peg_eval mmlPEG XX NONE` (K ALL_TAC)) >>
          asm_match
            `peg_eval mmlPEG (i0,nt (mkNT nType) I) (SOME(RparT::i1,r))`>>
          loseC ``NT_rank`` >>
          first_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          rpt kill_asm_guard >>
          disch_then (qxchl [`type_pt`] strip_assume_tac) >> rveq >> simp[] >>
          erule mp_tac
            (length_no_greater |> Q.GEN `sym` |> Q.ISPEC `nt (mkNT nType) I`
                               |> GEN_ALL) >> simp[] >> strip_tac >>
          fs[] >> `LENGTH i1 < SUC (LENGTH i0)` by decide_tac >>
          qpat_assum `peg_eval mmlPEG (II, rpt XX FF) YY` mp_tac >>
          simp[peg_eval_rpt] >> disch_then (qxchl [`tyops`] strip_assume_tac) >>
          rveq >> simp[] >>
          asm_match `peg_eval_list mmlPEG (i1, nt (mkNT nTyOp) I) (i,tyops)`>>
          pop_assum mp_tac >>
          `∃i2. LENGTH i2 < SUC (LENGTH i0) ∧ i1 = i2` by simp[] >>
          pop_assum SUBST1_TAC >> pop_assum mp_tac >>
          `∃acc.
             MAP ptree_head acc ∈ mmlG.rules ' (mkNT nDType) ∧
             (∀pt. MEM pt acc ⇒ valid_ptree mmlG pt) ∧
             TK LparT::(ptree_fringe type_pt ++ [TK RparT] ++ MAP TK i2) =
               FLAT (MAP ptree_fringe acc) ++ MAP TK i2 ∧
             [Lf (TK LparT); type_pt; Lf (TK RparT)] = acc`
            by simp[cmlG_FDOM, cmlG_applied, DISJ_IMP_THM, FORALL_AND_THM] >>
          ntac 2 (pop_assum SUBST1_TAC) >> ntac 2 (pop_assum mp_tac) >>
          map_every qid_spec_tac [`acc`, `i2`, `i`, `tyops`] >> Induct
          >- (simp[Once pegTheory.peg_eval_cases] >>
              simp[cmlG_FDOM, cmlG_applied]) >>
          map_every qx_gen_tac [`tyop`, `i`, `i2`, `acc`] >>
          simp[Once pegTheory.peg_eval_cases] >> ntac 3 strip_tac >>
          disch_then (qxchl [`i3`] strip_assume_tac) >>
          first_x_assum (erule mp_tac) >>
          disch_then (qxchl [`tyop_pt`] strip_assume_tac) >> rveq >>
          simp[] >>
          `LENGTH i3 < LENGTH i2`
            by metis_tac[not_peg0_LENGTH_decreases, peg0_nTyOp] >>
          `LENGTH i3 < SUC(LENGTH i0)` by decide_tac >>
          first_x_assum
            (qspecl_then [`i`, `i3`, `[Nd (mkNT nDType) acc; tyop_pt]`]
                         mp_tac)>>
          simp[cmlG_applied, cmlG_FDOM, DISJ_IMP_THM, FORALL_AND_THM]) >>
        (* tuple followed by at least one tyop case *)
        rpt (qpat_assum `peg_eval GG XX NONE` (K ALL_TAC)) >>
        loseC ``NT_rank`` >>
        asm_match `peg_eval mmlPEG (i1, nt (mkNT nTypeList2) I)
                      (SOME (RparT::i2, r))` >> fs[] >>
        first_assum (fn patth =>
          first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                       assert (free_in ``nTypeList2``) o concl)) >>
        rpt kill_asm_guard >>
        disch_then (qxchl [`tyl2_pt`] strip_assume_tac) >> rveq >> simp[] >>
        asm_match `peg_eval mmlPEG (i2, nt(mkNT nTyOp) I) (SOME(i3,r))` >>
        first_assum (mp_tac o MATCH_MP length_no_greater o
                     assert (free_in ``nTypeList2`` o concl)) >> simp[] >>
        strip_tac >> `LENGTH i2 < SUC (LENGTH i1)` by decide_tac >>
        first_assum (erule mp_tac) >>
        disch_then (qxchl [`tyop_pt`] strip_assume_tac) >> rveq >> simp[]>>
        first_assum (assume_tac o MATCH_MP length_no_greater o
                     assert (free_in ``nTyOp`` o concl) o
                     assert (free_in ``i2 : token list`` o concl)) >>
        `LENGTH i3 < SUC (LENGTH i1)` by decide_tac >>
        qpat_assum `peg_eval mmlPEG (II, rpt XX FF) YY` mp_tac >>
        simp[peg_eval_rpt] >> disch_then (qxchl [`tyops`] strip_assume_tac) >>
        rveq >> simp[] >>
        asm_match `peg_eval_list mmlPEG (i3, nt (mkNT nTyOp) I) (i,tyops)`>>
        pop_assum mp_tac >>
        `∃i4. LENGTH i4 < SUC (LENGTH i1) ∧ i3 = i4` by simp[] >>
        pop_assum SUBST1_TAC >> pop_assum mp_tac >>
        `∃acc.
           MAP ptree_head acc ∈ mmlG.rules ' (mkNT nDType) ∧
           (∀pt. MEM pt acc ⇒ valid_ptree mmlG pt) ∧
           TK LparT::(ptree_fringe tyl2_pt ++ [TK RparT] ++
                      ptree_fringe tyop_pt ++ MAP TK i4) =
             FLAT (MAP ptree_fringe acc) ++ MAP TK i4 ∧
           [Lf (TK LparT); tyl2_pt; Lf (TK RparT); tyop_pt] = acc`
          by simp[cmlG_FDOM, cmlG_applied, DISJ_IMP_THM, FORALL_AND_THM] >>
        ntac 2 (pop_assum SUBST1_TAC) >> ntac 2 (pop_assum mp_tac) >>
        map_every qid_spec_tac [`acc`, `i4`, `i`, `tyops`] >> Induct
        >- (simp[Once pegTheory.peg_eval_cases] >>
            simp[cmlG_FDOM, cmlG_applied]) >>
        map_every qx_gen_tac [`tyop`, `i`, `i4`, `acc`] >>
        simp[Once pegTheory.peg_eval_cases] >> ntac 3 strip_tac >>
        disch_then (qxchl [`i5`] strip_assume_tac) >>
        first_x_assum (erule mp_tac) >>
        disch_then (qxchl [`tyop_pt2`] strip_assume_tac) >> rveq >>
        simp[] >>
        `LENGTH i5 < LENGTH i4`
          by metis_tac[not_peg0_LENGTH_decreases, peg0_nTyOp] >>
        `LENGTH i5 < SUC(LENGTH i1)` by decide_tac >>
        first_x_assum
          (qspecl_then [`i`, `i5`, `[Nd (mkNT nDType) acc; tyop_pt2]`]
                       mp_tac)>>
        simp[cmlG_applied, cmlG_FDOM, DISJ_IMP_THM, FORALL_AND_THM])
  >- (print_tac "nType" >> simp[peg_Type_def, peg_eval_choice, sumID_def] >>
      `NT_rank (mkNT nDType) < NT_rank (mkNT nType)` by simp[NT_rank_def] >>
      strip_tac >> rveq >> simp[]
      >- (first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
          first_assum (assume_tac o MATCH_MP length_no_greater o
                       assert (free_in ``nDType`` o concl)) >> fs[] >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nType``) o concl)) >>
          asimp[] >> strip_tac >> rveq >> dsimp[cmlG_FDOM, cmlG_applied]) >>
      first_x_assum (erule strip_assume_tac) >> rveq >>
      dsimp[cmlG_applied, cmlG_FDOM])
  >- (print_tac "nFDecl" >> strip_tac >> rveq >> simp[] >>
      `NT_rank (mkNT nV) < NT_rank (mkNT nFDecl)` by simp[NT_rank_def] >>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      erule assume_tac
        (MATCH_MP not_peg0_LENGTH_decreases peg0_nV |> GEN_ALL) >>
      first_assum (erule strip_assume_tac) >> rveq >> dsimp[] >>
      first_assum (assume_tac o MATCH_MP length_no_greater o
                   assert (free_in ``nVlist1`` o concl)) >> fs[] >>
      first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nE``) o concl)) >>
      asimp[] >> strip_tac >> rveq >> simp[cmlG_FDOM, cmlG_applied])
  >- (print_tac "nAndFDecls" >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[SUBSET_DEF, pegsym_to_sym_def, DISJ_IMP_THM, FORALL_AND_THM,
           cmlG_applied, cmlG_FDOM] >> first_x_assum match_mp_tac >>
      simp[NT_rank_def])
  >- (print_tac "nPE'" >> strip_tac >> rveq >> simp[] >>
      `NT_rank (mkNT nPattern) < NT_rank (mkNT nPE')` by simp[NT_rank_def] >>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      first_assum (assume_tac o MATCH_MP length_no_greater o
                   assert (free_in ``nPattern`` o concl)) >> fs[] >>
      first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nE'``) o concl)) >>
      asimp[] >> strip_tac >> rveq >> dsimp[cmlG_FDOM, cmlG_applied])
  >- (print_tac "nPE" >> strip_tac >> rveq >> simp[] >>
      `NT_rank (mkNT nPattern) < NT_rank (mkNT nPE)` by simp[NT_rank_def] >>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      first_assum (assume_tac o MATCH_MP length_no_greater o
                   assert (free_in ``nPattern`` o concl)) >> fs[] >>
      first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nE``) o concl)) >>
      asimp[] >> strip_tac >> rveq >> dsimp[cmlG_FDOM, cmlG_applied])
  >- (print_tac "nPEs" >>
      `NT_rank (mkNT nPE') < NT_rank (mkNT nPEs) ∧
       NT_rank (mkNT nPE) < NT_rank (mkNT nPEs)`
         by simp[NT_rank_def] >>
      strip_tac >> rveq >> simp[] >> first_x_assum (erule strip_assume_tac) >>
      rveq >> simp[cmlG_applied, cmlG_FDOM] >>
      first_assum (assume_tac o MATCH_MP length_no_greater o
                   assert (free_in ``nPE'`` o concl)) >> fs[] >>
      first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nPEs``) o concl)) >>
      asimp[] >> strip_tac >> rveq >> dsimp[])
  >- (print_tac "nE'" >> strip_tac >> rveq >> simp[] >> fs[]
      >- ((* raise case *)
          loseC ``NT_rank`` >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          simp[] >> strip_tac >> rveq >> dsimp[cmlG_FDOM, cmlG_applied])
      >- ((* Ehandle' case *)
          loseC ``LENGTH`` >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          simp[NT_rank_def] >> strip_tac >> rveq >>
          dsimp[cmlG_FDOM, cmlG_applied])
      >- ((* if-then-else case *) loseC ``NT_rank`` >>
          first_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``ThenT``) o concl)) >>
          rpt kill_asm_guard >> strip_tac >> rveq >> simp[] >>
          first_assum (assume_tac o MATCH_MP length_no_greater o
                       assert (free_in ``ThenT`` o concl)) >> fs[] >>
          first_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``ElseT``) o concl)) >>
          rpt kill_asm_guard >> strip_tac >> rveq >> simp[] >>
          first_assum (assume_tac o MATCH_MP length_no_greater o
                       assert (free_in ``ElseT`` o concl)) >> fs[] >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nE'``) o concl)) >>
          rpt kill_asm_guard >> strip_tac >> rveq >>
          dsimp[cmlG_applied, cmlG_FDOM])
      >- ((* fn x => e case *) loseC ``NT_rank`` >>
          rpt (qpat_assum `peg_eval G X NONE` (K ALL_TAC)) >>
          first_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nV``) o concl)) >>
          rpt kill_asm_guard >> strip_tac >> rveq >>
          first_assum (assume_tac o MATCH_MP length_no_greater o
                       assert (free_in ``nV`` o concl)) >> fs[] >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nE'``) o concl)) >>
          asimp[] >> strip_tac >> rveq >> dsimp[cmlG_FDOM, cmlG_applied]) >>
      (* bogus raise Ehandle' case *)
      loseC ``LENGTH`` >> first_x_assum (fn patth =>
        first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
      simp[NT_rank_def] >> strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM])
  >- (print_tac "nE" >> strip_tac >> rveq >> simp[] >> fs[]
      >- ((* raise E case *)
          loseC ``NT_rank`` >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          simp[] >> strip_tac >> rveq >> dsimp[cmlG_FDOM, cmlG_applied])
      >- ((* handle case *)
          loseC ``LENGTH`` >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          simp[NT_rank_def] >> strip_tac >> rveq >>
          dsimp[cmlG_FDOM, cmlG_applied])
      >- ((* if then else case *)
          first_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``ThenT``) o concl)) >>
          rpt kill_asm_guard >> strip_tac >> rveq >> simp[] >>
          first_assum (assume_tac o MATCH_MP length_no_greater o
                       assert (free_in ``ThenT`` o concl)) >> fs[] >>
          first_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``ElseT``) o concl)) >>
          rpt kill_asm_guard >> strip_tac >> rveq >> simp[] >>
          first_assum (assume_tac o MATCH_MP length_no_greater o
                       assert (free_in ``ElseT`` o concl)) >> fs[] >>
          dsimp[cmlG_applied, cmlG_FDOM, MAP_EQ_SING] >> csimp[] >>
          qpat_assum `peg_eval mmlPEG X (SOME(ThenT::Y,Z))` (K ALL_TAC) >>
          qpat_assum `peg_eval mmlPEG X (SOME(ElseT::Y,Z))` (K ALL_TAC) >>
          loseC ``NT_rank`` >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          asimp[] >> metis_tac[])
      >- ((* fn x => e case *) loseC ``NT_rank`` >>
          rpt (qpat_assum `peg_eval G X NONE` (K ALL_TAC)) >>
          first_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nV``) o concl)) >>
          rpt kill_asm_guard >> strip_tac >> rveq >>
          first_assum (assume_tac o MATCH_MP length_no_greater o
                       assert (free_in ``nV`` o concl)) >> fs[] >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nE``) o concl)) >>
          asimp[] >> strip_tac >> rveq >> dsimp[cmlG_FDOM, cmlG_applied])
      >- ((* "case" E "of" PEs case *) loseC ``NT_rank`` >>
          rpt (qpat_assum `peg_eval G X NONE` (K ALL_TAC)) >>
          first_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nE``) o concl)) >>
          rpt kill_asm_guard >> strip_tac >> rveq >> simp[] >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nPEs``) o concl)) >>
          first_assum (assume_tac o MATCH_MP length_no_greater o
                       assert (free_in ``nE`` o concl)) >> fs[] >>
          asimp[] >> strip_tac >> rveq >> dsimp[cmlG_applied, cmlG_FDOM]) >>
      (* raise-ehandle case *)
      loseC ``LENGTH`` >> first_x_assum (fn patth =>
        first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
      simp[NT_rank_def] >> strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM])
  >- (print_tac "nEhandle'" >>
      `NT_rank (mkNT nElogicOR) < NT_rank (mkNT nEhandle')`
        by simp[NT_rank_def] >>
      strip_tac >> rveq >> simp[] >>
      first_x_assum (erule strip_assume_tac) >> rveq >>
      dsimp[cmlG_FDOM, cmlG_applied] >>
      first_assum (assume_tac o MATCH_MP length_no_greater o
                   assert (free_in ``nElogicOR`` o concl)) >> fs[] >>
      first_assum (fn patth =>
         first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                      assert (free_in ``nV``) o concl)) >>
      rpt kill_asm_guard >> strip_tac >> rveq >>
      first_assum (assume_tac o MATCH_MP length_no_greater o
                   assert (free_in ``nV`` o concl)) >> fs[] >>
      first_x_assum (fn patth =>
         first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                      assert (free_in ``nE'``) o concl)) >>
      asimp[] >> strip_tac >> rveq >> simp[])
  >- (print_tac "nEhandle" >>
      `NT_rank (mkNT nElogicOR) < NT_rank (mkNT nEhandle)`
        by simp[NT_rank_def] >>
      strip_tac >> rveq >> simp[] >>
      first_x_assum (erule strip_assume_tac) >> rveq >>
      dsimp[cmlG_FDOM, cmlG_applied] >>
      first_assum (assume_tac o MATCH_MP length_no_greater o
                   assert (free_in ``nElogicOR`` o concl)) >> fs[] >>
      first_assum (fn patth =>
         first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                      assert (free_in ``nV``) o concl)) >>
      rpt kill_asm_guard >> strip_tac >> rveq >>
      first_assum (assume_tac o MATCH_MP length_no_greater o
                   assert (free_in ``nV`` o concl)) >> fs[] >>
      first_x_assum (fn patth =>
         first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                      assert (free_in ``nE``) o concl)) >>
      asimp[] >> strip_tac >> rveq >> simp[])
  >- (print_tac "nElogicOR" >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[cmlG_applied, cmlG_FDOM, pegsym_to_sym_def, DISJ_IMP_THM,
           FORALL_AND_THM, SUBSET_DEF] >> simp[NT_rank_def])
  >- (print_tac "nElogicAND" >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[cmlG_applied, cmlG_FDOM, pegsym_to_sym_def, DISJ_IMP_THM,
           FORALL_AND_THM, SUBSET_DEF] >> simp[NT_rank_def])
  >- (print_tac "nEtyped" >>
      `NT_rank (mkNT nEbefore) < NT_rank (mkNT nEtyped)`
        by simp[NT_rank_def] >> strip_tac >> rveq >>
      simp[cmlG_FDOM, cmlG_applied] >>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      first_x_assum (assume_tac o MATCH_MP length_no_greater o
                     assert (free_in ``nEbefore`` o concl)) >> fs[] >>
      first_x_assum (fn patth =>
         first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                      assert (free_in ``nType``) o concl)) >> asimp[] >>
      strip_tac >> rveq >> dsimp[])
  >- (print_tac "nEbefore" >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[cmlG_applied, cmlG_FDOM, pegsym_to_sym_def, DISJ_IMP_THM,
           FORALL_AND_THM, SUBSET_DEF] >> simp[NT_rank_def])
  >- (print_tac "nEcomp" >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[cmlG_applied, cmlG_FDOM, pegsym_to_sym_def, DISJ_IMP_THM,
           FORALL_AND_THM, SUBSET_DEF] >> simp[NT_rank_def])
  >- (print_tac "nErel" >> simp[peg_nonfix_def] >>
      `NT_rank (mkNT nEadd) < NT_rank (mkNT nErel)` by simp[NT_rank_def]>>
      strip_tac >> rveq >> simp[] >>
      first_x_assum (erule strip_assume_tac) >> rveq >>
      dsimp[cmlG_FDOM, cmlG_applied] >>
      first_x_assum
        (assume_tac o
         MATCH_MP (GEN_ALL (MATCH_MP not_peg0_LENGTH_decreases peg0_nEadd)) o
         assert (free_in ``NIL : mlptree list`` o concl)) >>
      first_assum (fn patth =>
         first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                      assert (free_in ``nRelOps``) o concl)) >>
      rpt kill_asm_guard >> strip_tac >> rveq >> dsimp[] >>
      first_x_assum (assume_tac o MATCH_MP length_no_greater o
                     assert (free_in ``nRelOps`` o concl)) >> fs[] >>
      first_x_assum (fn patth =>
         first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                      assert (free_in ``nEadd``) o concl)) >>
      rpt kill_asm_guard >> strip_tac >> rveq >> simp[])
  >- (print_tac "nEadd" >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[cmlG_applied, cmlG_FDOM, pegsym_to_sym_def, DISJ_IMP_THM,
           FORALL_AND_THM, SUBSET_DEF] >> simp[NT_rank_def])
  >- (print_tac "nEmult" >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[cmlG_applied, cmlG_FDOM, pegsym_to_sym_def, DISJ_IMP_THM,
           FORALL_AND_THM, SUBSET_DEF] >> simp[NT_rank_def])
  >- (print_tac "nEseq" >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[cmlG_applied, cmlG_FDOM, pegsym_to_sym_def, DISJ_IMP_THM,
           FORALL_AND_THM, SUBSET_DEF] >> simp[NT_rank_def])
  >- (print_tac "nEbase" >>
      `NT_rank (mkNT nFQV) < NT_rank (mkNT nEbase) ∧
       NT_rank (mkNT nConstructorName) < NT_rank (mkNT nEbase)`
        by simp[NT_rank_def] >> strip_tac >> rveq >>
      simp[cmlG_FDOM, cmlG_applied] >> fs[] >>
      rpt (qpat_assum `peg_eval G X NONE` (K ALL_TAC))
      >- (asm_match `isInt h` >> Cases_on `h` >> fs[])
      >- (first_x_assum (erule strip_assume_tac) >> rveq >> simp[])
      >- (first_x_assum (erule strip_assume_tac) >> rveq >> simp[])
      >- dsimp[] (* "(" ")" case *)
      >- ((*seq case *) rpt (loseC ``NT_rank``) >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          simp[] >> strip_tac >> rveq >> dsimp[])
      >- ((* "let" ... "in" ... "end" case *)
          rpt (loseC ``NT_rank``) >>
          first_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nLetDecs``) o concl)) >>
          rpt kill_asm_guard >> strip_tac >> rveq >> dsimp[] >>
          first_x_assum (assume_tac o MATCH_MP length_no_greater o
                         assert (free_in ``nLetDecs`` o concl)) >> fs[] >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          rpt kill_asm_guard >> strip_tac >> rveq >> dsimp[]) >>
      (* eseq in parens case *) rveq >>
      first_x_assum (fn patth =>
        first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
      rpt kill_asm_guard >> strip_tac >> rveq >> dsimp[])
  >- (print_tac "nCompOps">> strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM])
  >- (print_tac "nRelOps" >> strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM])
  >- (print_tac "nAddOps" >> strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM])
  >- (print_tac "nMultOps">> strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM])
  >- (print_tac "nElist1" >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[cmlG_applied, cmlG_FDOM, pegsym_to_sym_def, DISJ_IMP_THM,
           FORALL_AND_THM, SUBSET_DEF] >> simp[NT_rank_def])
  >- (print_tac "nElist2" >> strip_tac >> rveq >>
      dsimp[cmlG_FDOM, cmlG_applied] >>
      `NT_rank (mkNT nE) < NT_rank (mkNT nElist2)` by simp[NT_rank_def] >>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      first_x_assum (assume_tac o MATCH_MP length_no_greater o
                     assert (free_in ``nE`` o concl)) >> fs[] >>
      first_x_assum (fn patth =>
        first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
      rpt kill_asm_guard >> strip_tac >> rveq >> simp[])
  >- (print_tac "nEtuple" >> loseC ``NT_rank`` >> strip_tac >> rveq >>
      dsimp[cmlG_applied, cmlG_FDOM] >>
      first_x_assum (fn patth =>
        first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
      rpt kill_asm_guard >> strip_tac >> rveq >> simp[])
  >- (print_tac "nEapp" >> simp[peg_Eapp_def, peg_eval_choice] >>
      strip_tac >> rpt (qpat_assum `peg_eval X Y NONE` (K ALL_TAC)) >>
      rveq >> simp[sumID_def]
      >- (`NT_rank (mkNT nConstructorName) < NT_rank (mkNT nEapp)`
            by simp[NT_rank_def] >>
          first_x_assum (erule strip_assume_tac) >> rveq >>
          dsimp[cmlG_FDOM, cmlG_applied] >>
          erule assume_tac
            (MATCH_MP not_peg0_LENGTH_decreases peg0_nConstructorName
                      |> GEN_ALL) >>
          first_x_assum (erule strip_assume_tac) >> rveq >> simp[])
      >- (fs[sumID_def] >> rveq >> simp[] >>
          `NT_rank (mkNT nEbase) < NT_rank (mkNT nEapp)` by simp[NT_rank_def]>>
          first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
          erule assume_tac
            (MATCH_MP not_peg0_LENGTH_decreases peg0_nEbase |> GEN_ALL) >>
          asm_match `peg_eval mmlPEG (i0, nt (mkNT nEbase) I) (SOME(i1,[pt]))`>>
          asm_match
            `peg_eval mmlPEG (i1,rpt(nt(mkNT nEbase) I) FLAT) (SOME(i,r))` >>
          qpat_assum `peg_eval G (i1, rpt X R) Y` mp_tac >>
          simp[peg_eval_rpt] >> disch_then (qxchl [`pts`] strip_assume_tac) >>
          rveq >>
          `∃acc. ptree_fringe pt = FLAT (MAP ptree_fringe acc) ∧
                 [pt] = acc ∧ MAP ptree_head acc ∈ mmlG.rules ' (mkNT nEapp) ∧
                 (∀pt. MEM pt acc ⇒ valid_ptree mmlG pt)`
            by simp[cmlG_applied, cmlG_FDOM] >>
          ntac 2 (pop_assum mp_tac) >> ntac 2 (pop_assum SUBST1_TAC) >>
          Q.UNDISCH_THEN `LENGTH i1 < LENGTH i0` mp_tac >>
          qpat_assum `peg_eval_list X Y Z` mp_tac >>
          map_every qid_spec_tac [`i`, `i1`, `acc`, `pts`] >> Induct
          >- (simp[Once pegTheory.peg_eval_cases, cmlG_FDOM]) >>
          simp[Once pegTheory.peg_eval_cases] >>
          map_every qx_gen_tac [`pt'`, `acc`, `i2`, `i`] >>
          disch_then (qxchl [`i3`] strip_assume_tac) >>
          ntac 3 strip_tac >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``pt':mlptree list``) o concl)) >>
          rpt kill_asm_guard >> disch_then (qxchl [`ebpt`] strip_assume_tac) >>
          rveq >> simp[] >>
          first_x_assum (assume_tac o MATCH_MP length_no_greater o
                         assert (free_in ``ebpt:mlptree`` o concl)) >>
          first_x_assum
            (qspecl_then [`[Nd (mkNT nEapp) acc; ebpt]`, `i3`, `i`]
                         mp_tac) >>
          rpt kill_asm_guard >> dsimp[cmlG_FDOM, cmlG_applied]) >>
      rveq >> simp[sumID_def] >>
      `NT_rank (mkNT nEbase) < NT_rank (mkNT nEapp)` by simp[NT_rank_def]>>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      erule assume_tac
        (MATCH_MP not_peg0_LENGTH_decreases peg0_nEbase |> GEN_ALL) >>
      loseC ``nConstructorName`` >>
      asm_match `peg_eval mmlPEG (i0, nt (mkNT nEbase) I) (SOME(i1,[pt]))`>>
      asm_match
        `peg_eval mmlPEG (i1,rpt(nt(mkNT nEbase) I) FLAT) (SOME(i,r))` >>
      qpat_assum `peg_eval G (i1, rpt X R) Y` mp_tac >>
      simp[peg_eval_rpt] >> disch_then (qxchl [`pts`] strip_assume_tac) >>
      rveq >>
      `∃acc. ptree_fringe pt = FLAT (MAP ptree_fringe acc) ∧
             [pt] = acc ∧ MAP ptree_head acc ∈ mmlG.rules ' (mkNT nEapp) ∧
             (∀pt. MEM pt acc ⇒ valid_ptree mmlG pt)`
        by simp[cmlG_applied, cmlG_FDOM] >>
      ntac 2 (pop_assum mp_tac) >> ntac 2 (pop_assum SUBST1_TAC) >>
      Q.UNDISCH_THEN `LENGTH i1 < LENGTH i0` mp_tac >>
      qpat_assum `peg_eval_list X Y Z` mp_tac >>
      map_every qid_spec_tac [`i`, `i1`, `acc`, `pts`] >> Induct
      >- (simp[Once pegTheory.peg_eval_cases, cmlG_FDOM]) >>
      simp[Once pegTheory.peg_eval_cases] >>
      map_every qx_gen_tac [`pt'`, `acc`, `i2`, `i`] >>
      disch_then (qxchl [`i3`] strip_assume_tac) >>
      ntac 3 strip_tac >>
      first_x_assum (fn patth =>
        first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                     assert (free_in ``pt':mlptree list``) o concl)) >>
      rpt kill_asm_guard >> disch_then (qxchl [`ebpt`] strip_assume_tac) >>
      rveq >> simp[] >>
      first_x_assum (assume_tac o MATCH_MP length_no_greater o
                     assert (free_in ``ebpt:mlptree`` o concl)) >>
      first_x_assum
        (qspecl_then [`[Nd (mkNT nEapp) acc; ebpt]`, `i3`, `i`]
                     mp_tac) >>
      rpt kill_asm_guard >> dsimp[cmlG_FDOM, cmlG_applied])
  >- (print_tac "nExn" >> strip_tac >> rveq >> dsimp[cmlG_applied, cmlG_FDOM]>>
      asm_match `isInt itok` >> Cases_on `itok` >> fs[])
  >- (print_tac "nFQV" >>
      simp[peg_longV_def, pairTheory.EXISTS_PROD, gramTheory.assert_def] >>
      strip_tac >> rveq >> dsimp[cmlG_FDOM, cmlG_applied]
      >- (`NT_rank (mkNT nV) < NT_rank (mkNT nFQV)` by simp[NT_rank_def] >>
          first_x_assum (erule strip_assume_tac) >> rveq >> simp[]) >>
      asm_match `destLongidT litok = SOME(mp,vp)` >> Cases_on `litok` >> fs[])
  >- (print_tac "nVlist1" >> strip_tac >> rveq >>
      dsimp[cmlG_applied, cmlG_FDOM] >>
      `NT_rank (mkNT nV) < NT_rank (mkNT nVlist1)` by simp[NT_rank_def] >>
      first_x_assum (erule strip_assume_tac) >> rveq >> dsimp[] >>
      first_x_assum
        (assume_tac o
         (peg0_nV |> MATCH_MP not_peg0_LENGTH_decreases |> GEN_ALL
                  |> MATCH_MP)) >>
      first_x_assum (fn patth =>
        first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
      rpt kill_asm_guard >> strip_tac >> rveq >> simp[])
  >- (print_tac "nTyvarN" >> rw[] >> simp[cmlG_FDOM, cmlG_applied] >>
      asm_match `isTyvarT h` >> Cases_on `h` >> fs[]) >>
  print_tac "nV" >>
  simp[peg_V_def, peg_eval_choice, sumID_def, gramTheory.assert_def] >>
  strip_tac >> rveq >> dsimp[cmlG_FDOM, cmlG_applied]
  >- (asm_match `destAlphaT t = SOME astring` >> Cases_on `t` >> fs[]) >>
  asm_match `destSymbolT mytok = SOME symstring` >>
  Cases_on `mytok` >>fs[])

val _ = export_theory()
