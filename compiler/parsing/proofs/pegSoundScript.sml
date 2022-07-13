(*
  Soundness proof for the parser. If the parser returns a parse tree,
  then it is valid w.r.t. the specification grammar.
*)
open preamble pegTheory cmlPEGTheory gramTheory gramPropsTheory
     grammarTheory

val _ = new_theory "pegSound";
val _ = set_grammar_ancestry ["cmlPEG", "gramProps"]

infix >*
fun t1 >* t2 = (t1 >> conj_tac) >- t2

val _ = hide "choicel"
Overload choicel = “cmlPEG$choicel”

Theorem Success_COND_Failure[simp]:
  Success i r opt ≠ if P then Failure fl1 fe1 else Failure fl2 fe2
Proof
  simp[AllCaseEqs()]
QED

Theorem peg_eval_choicel_NIL[simp]:
   peg_eval G (i0, choicel []) x ⇔ x = Failure (sloc i0) G.notFAIL
Proof
  simp[choicel_def, Once peg_eval_cases]
QED

Theorem peg_TF:
  (∃i' r eopt. peg_eval G (i,e) (Success i' r eopt))  ⇒
  ¬peg_eval G (i,e) (Failure fl fe)
Proof
  metis_tac[peg_deterministic, TypeBase.distinct_of “:(α,β,γ)pegresult”]
QED

Theorem peg_FT:
  (∃fl fe. peg_eval G (i,e) (Failure fl fe)) ⇒
  ¬peg_eval G (i,e) (Success i' r eopt)
Proof
  metis_tac[peg_deterministic, TypeBase.distinct_of “:(α,β,γ)pegresult”]
QED

Theorem peg_eval_choicel_CONS:
  ∀x. peg_eval G (i0, choicel (h::t)) x ⇔
        (∃i r eopt.
           peg_eval G (i0, h) (Success i r eopt) ∧ x = Success i r eopt) ∨
        (∃res2 fl1 fe1 i r eopt fl2 fe2.
           peg_eval G (i0,h) (Failure fl1 fe1) ∧
           peg_eval G (i0,choicel t) res2 ∧
           (res2 = Success i r eopt ∧
            x = Success i r (optmax MAXerr (SOME (fl1,fe1)) eopt) ∨
            res2 = Failure fl2 fe2 ∧
            x = UNCURRY Failure (MAXerr (fl1, fe1) (fl2,fe2))))
Proof
  simp[choicel_def, SimpLHS, Once peg_eval_cases] >>
  dsimp[EQ_IMP_THM, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS,
        FORALL_result, EXISTS_result, AllCaseEqs()] >>
  SRW_TAC[SatisfySimps.SATISFY_ss][peg_TF, sumID_def, peg_FT] >>
  metis_tac[]
QED

Theorem peg_eval_seql_NIL[simp]:
   peg_eval G (i0, seql [] f) x ⇔ x = Success i0 (f []) NONE
Proof
  simp[seql_def, pegf_def] >> csimp[Once peg_eval_cases]
QED

Theorem peg_eval_try:
  ∀x. peg_eval G (i0, try s) x ⇔
        (∃fl fe. peg_eval G (i0, s) (Failure fl fe) ∧
                 x = Success i0 [] (optmax MAXerr (SOME (fl,fe)) NONE)) ∨
        ∃i r eo. peg_eval G (i0, s) (Success i r eo) ∧ x = Success i r eo
Proof
  simp[Once peg_eval_cases, try_def, SimpLHS, choicel_def,
       peg_eval_choice] >> simp[sumID_def, EXISTS_result] >>
  metis_tac[]
QED

Theorem peg_eval_seql_CONS:
  ∀x. peg_eval G (i0, seql (h::t) f) x ⇔
        (∃fl fe. peg_eval G (i0, h) (Failure fl fe) ∧ x = Failure fl fe) ∨
        (∃rh i1 fl fe eopt.
           peg_eval G (i0,h) (Success i1 rh eopt) ∧
           peg_eval G (i1, seql t I) (Failure fl fe) ∧ x = Failure fl fe) ∨
        (∃rh i1 i rt eopt1 eopt2.
           peg_eval G (i0, h) (Success i1 rh eopt1) ∧
           peg_eval G (i1, seql t I) (Success i rt eopt2) ∧
           x = Success i (f(rh ++ rt)) eopt2)
Proof
  simp[seql_def, pegf_def] >>
  simp[SimpLHS, Once peg_eval_cases] >>
  csimp[FORALL_result, peg_eval_seq_NONE, peg_eval_seq_SOME, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem peg_eval_choicel_SING =
  CONJ
    (``peg_eval G (i0, choicel [sym]) (Success i r eo)``
       |> SIMP_CONV (srw_ss()) [peg_eval_choicel_CONS, peg_eval_choicel_NIL,
                                AllCaseEqs()])
    (``peg_eval G (i0, choicel [sym]) (Failure fl fe)``
       |> SIMP_CONV (srw_ss()) [peg_eval_choicel_CONS, peg_eval_choicel_NIL,
                                AllCaseEqs()]);

Theorem not_peg0_LENGTH_decreases:
   ¬peg0 G s ⇒ peg_eval G (i0, s) (Success i r eo) ⇒ LENGTH i < LENGTH i0
Proof
  metis_tac[peg_eval_suffix', lemma4_1a]
QED

val _ = augment_srw_ss [rewrites [
  peg_eval_seql_CONS, peg_eval_tok_SOME, tokeq_def, bindNT_def, mktokLf_def,
  peg_eval_choicel_CONS, pegf_def, peg_eval_seq_SOME, pnt_def, peg_eval_try,
  try_def,resultmap_EQ_Success]]

Theorem peg_eval_tokSymP[simp]:
  peg_eval G (i0, tokSymP P) (Success i r eo) ⇔
  ∃h s. FST h = SymbolT s ∧ P s ∧ i0 = h::i ∧ r = mktokLf h ∧ eo = NONE
Proof
  simp[tokSymP_def, PULL_EXISTS, EXISTS_PROD]
QED

Theorem FADISJ_EQ_IMP'[simp,local]:
  ((∀x. P x) ∨ Q ⇔ ∀x. ~P x ⇒ Q) ∧
  ((Q ∨ ∀x. P x) ⇔ ∀x. ~P x ⇒ Q)
Proof
  metis_tac[]
QED

Theorem peg_eval_TypeDec_wrongtok:
   FST tk ≠ DatatypeT ⇒
   ¬peg_eval cmlPEG (tk::i, nt (mkNT nTypeDec) f) (Success i' r eo)
Proof
  simp[Once peg_eval_cases, cmlpeg_rules_applied, FDOM_cmlPEG,
       peg_TypeDec_def, tokeq_def, peg_eval_tok_SOME] >> rw[] >>
  gs[]
QED

Theorem peg_eval_TypeAbbrevDec_wrongtok:
   FST tk ≠ TypeT ⇒
   ¬peg_eval cmlPEG (tk::i, nt (mkNT nTypeAbbrevDec) f) (Success i' r eo)
Proof
  simp[Once peg_eval_cases, cmlpeg_rules_applied, FDOM_cmlPEG,
       peg_eval_seq_SOME, tokeq_def, peg_eval_tok_SOME] >> rw[] >> gs[]
QED

Theorem peg_eval_Structure_wrongtok:
  FST tk ≠ StructureT ⇒
  ¬peg_eval cmlPEG (tk::i, nt (mkNT nStructure) f) (Success i' r e0)
Proof
  simp[Once peg_eval_cases, cmlpeg_rules_applied, FDOM_cmlPEG,
       peg_eval_seq_SOME, tokeq_def, peg_eval_tok_SOME] >> rw[] >> gs[]
QED



Theorem peg_eval_LetDec_wrongtok:
   FST tk = SemicolonT ⇒
   ¬peg_eval cmlPEG (tk::i, nt (mkNT nLetDec) f) (Success i' r eo)
Proof
  simp[Once peg_eval_cases, cmlpeg_rules_applied, FDOM_cmlPEG,
       peg_TypeDec_def, peg_eval_seq_SOME, tokeq_def, peg_eval_tok_SOME,
       peg_eval_choicel_CONS, peg_eval_seql_CONS,
       AllCaseEqs()] >> rw[] >> gs[]
QED

Theorem peg_eval_nUQConstructor_wrongtok:
   (∀s. FST t ≠ AlphaT s) ⇒
    ¬peg_eval cmlPEG (t::i, nt (mkNT nUQConstructorName) f) (Success i' r eo)
Proof
  simp[Once peg_eval_cases, cmlpeg_rules_applied, peg_eval_tok_SOME,
       peg_UQConstructorName_def] >> Cases_on `t` >> simp[]
QED

Theorem peg_eval_nConstructor_wrongtok:
   (∀s. FST t ≠ AlphaT s) ∧ (∀s1 s2. FST t ≠ LongidT s1 s2) ⇒
   ¬peg_eval cmlPEG (t::i, nt (mkNT nConstructorName) f) (Success i' r eo)
Proof
  simp[Once peg_eval_cases, cmlpeg_rules_applied, peg_eval_tok_SOME,
       peg_eval_choicel_CONS, peg_eval_seq_NONE, pegf_def, pnt_def,
       peg_eval_nUQConstructor_wrongtok, peg_eval_seq_SOME,
       EXISTS_PROD, PULL_EXISTS] >> rw[] >> gs[]
QED

Theorem peg_eval_nV_wrongtok:
   (∀s. FST t ≠ AlphaT s) ∧ (∀s. FST t ≠ SymbolT s) ⇒
    ¬peg_eval cmlPEG (t::i, nt (mkNT nV) f) (Success i' r eo)
Proof
  simp[Once peg_eval_cases, cmlpeg_rules_applied, peg_V_def,
       peg_eval_seq_NONE, peg_eval_choice] >> rw[] >> gs[]
QED

Theorem peg_eval_nFQV_wrongtok:
  (∀s. FST t ≠ AlphaT s) ∧ (∀s. FST t ≠ SymbolT s) ∧
  (∀s1 s2. FST t ≠ LongidT s1 s2) ⇒
  ¬peg_eval cmlPEG (t::i, nt (mkNT nFQV) f) (Success i' r eo)
Proof
  simp[Once peg_eval_cases, cmlpeg_rules_applied, peg_longV_def, EXISTS_PROD,
       peg_eval_seq_NONE, peg_eval_choice, peg_eval_nV_wrongtok, PULL_EXISTS] >>
  rw[] >> gs[]
QED

Theorem peg_eval_rpt_never_NONE[simp]:
   ¬peg_eval G (i, rpt sym f) (Failure fl fe)
Proof
  simp[Once peg_eval_cases]
QED

Definition pegsym_to_sym_def:
  (pegsym_to_sym (tok P f) = if f = mktokLf then { TK t | P t } else ∅) ∧
  pegsym_to_sym (nt N f) = { NT N } ∧
  pegsym_to_sym _ = {}
End

Theorem valid_ptree_mkNd[simp]:
   valid_ptree G (mkNd N subs) ⇔
     N ∈ FDOM G.rules ∧ MAP ptree_head subs ∈ G.rules ' N ∧
     ∀pt. MEM pt subs ⇒ valid_ptree G pt
Proof
  simp[mkNd_def]
QED

Theorem ptree_head_mkNd[simp]:
   ptree_head (mkNd N subs) = NT N
Proof
  simp[mkNd_def]
QED

val ptree_list_loc_def = grammarTheory.ptree_list_loc_def
Theorem ptree_list_loc_SING[simp]:
   ptree_list_loc [pt] = ptree_loc pt
Proof
  simp[ptree_list_loc_def]
QED

Theorem ptree_fringe_mkNd[simp]:
   ptree_fringe (mkNd N subs) = FLAT (MAP ptree_fringe subs)
Proof
  simp[mkNd_def]
QED

Theorem valid_locs_mkNd[simp]:
   valid_locs (mkNd N subs) ⇔ ∀pt. MEM pt subs ⇒ valid_locs pt
Proof
  simp[mkNd_def, ptree_list_loc_def]
QED

Theorem rfringe_length_not_nullable:
   ∀G s. ¬nullable G [s] ⇒
         ∀pt. ptree_head pt = s ⇒ valid_lptree G pt ⇒
              0 < LENGTH (real_fringe pt)
Proof
  metis_tac[fringe_length_not_nullable, LENGTH_real_fringe, valid_lptree_def]
QED

Theorem valid_lptree_mkNd[simp]:
   valid_lptree G (mkNd n children) ⇔
      n ∈ FDOM G.rules ∧ MAP ptree_head children ∈ G.rules ' n ∧
      ∀pt. MEM pt children ⇒ valid_lptree G pt
Proof
  simp[mkNd_def, ptree_list_loc_def]
QED

Theorem real_fringe_mkNd[simp]:
   real_fringe (mkNd n subs) = FLAT (MAP real_fringe subs)
Proof
  simp[mkNd_def] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM]
QED

Theorem ptree_head_NT_mkNd:
   ptree_head pt = NN n ∧ valid_lptree cmlG pt ∧
   real_fringe pt = MAP (TK ## I) pf ⇒
   ∃subs. pt = mkNd (mkNT n) subs
Proof
  Cases_on `pt`
  >- (rename [`ptree_head (Lf pair)`] >> Cases_on `pair` >> simp[] >>
      rw[valid_lptree_def] >> rename [`(NN _, _) = (TK ## I) pair`] >>
      Cases_on `pair` >> fs[]) >>
  rename [`ptree_head (Nd pair _)`] >> Cases_on `pair` >>
  simp[MAP_EQ_CONS, mkNd_def, ptree_list_loc_def]
QED

Theorem mkNd_11[simp]:
   mkNd n1 sub1 = mkNd n2 sub2 ⇔ n1 = n2 ∧ sub1 = sub2
Proof
  csimp[mkNd_def]
QED

Theorem peg_linfix_correct_lemma:
   ∀UpperN sym sepsym i0 i pts eo.
      peg_eval cmlPEG (i0, peg_linfix UpperN sym sepsym) (Success i pts eo) ⇒
      (∀i0' i pts s eo.
         s ∈ {sym;sepsym} ⇒
         LENGTH i0' < LENGTH i0 ⇒
         peg_eval cmlPEG (i0',s) (Success i pts eo) ⇒
         ∃pt. pts = [pt] ∧ ptree_head pt ∈ pegsym_to_sym s ∧
              valid_lptree cmlG pt ∧
              MAP (TK ## I) i0' = real_fringe pt ++ MAP (TK ## I) i) ∧
      (∀i pts s eo.
         s ∈ {sym; sepsym} ⇒
         peg_eval cmlPEG (i0, s) (Success i pts eo) ⇒
         ∃pt. pts = [pt] ∧ ptree_head pt ∈ pegsym_to_sym s ∧
              valid_lptree cmlG pt ∧
              MAP (TK ## I) i0 = real_fringe pt ++ MAP (TK ## I) i) ∧
      ¬peg0 cmlPEG sym ∧
      UpperN ∈ FDOM cmlG.rules ∧
      {[gsym] | gsym ∈ pegsym_to_sym sym } ⊆ cmlG.rules ' UpperN ∧
      {[NT UpperN; gsep; gsym] |
          gsep ∈ pegsym_to_sym sepsym ∧ gsym ∈ pegsym_to_sym sym } ⊆
        cmlG.rules ' UpperN ⇒
      ∃pt. pts = [pt] ∧ ptree_head pt = NT UpperN ∧ valid_lptree cmlG pt ∧
           MAP (TK ## I) i0 = real_fringe pt ++ MAP (TK ## I) i
Proof
  rpt strip_tac >> qpat_x_assum `peg_eval X Y Z` mp_tac >>
  simp[peg_linfix_def, peg_eval_rpt, peg_eval_seq_SOME] >>
  rpt strip_tac >> rveq >> simp[AllCaseEqs(), PULL_EXISTS] >>
  rename [‘peg_eval cmlPEG (i0, sym) (Success i1 r1 eo1)’] >>
  first_assum (drule_at (Pos (el 2))) >> simp_tac(srw_ss())[]>>
  ASM_REWRITE_TAC[] >> disch_then (qxchl[`rpt1`] strip_assume_tac) >> simp[] >>
  rveq >>
  qpat_x_assum `peg_eval_list X Y Z` mp_tac >>
  `∃i2. i2 = i1 ∧ LENGTH i2 ≤ LENGTH i1` by simp[] >>
  Q.UNDISCH_THEN `i2 = i1` (SUBST1_TAC o SYM) >>
  `∃acc. MAP ptree_head acc ∈ cmlG.rules ' UpperN ∧
         (∀pt. MEM pt acc ⇒ valid_lptree cmlG pt) ∧
         [rpt1] = acc ∧ real_fringe rpt1 = FLAT (MAP real_fringe acc)`
    by (simp[] >> fs[SUBSET_DEF]) >>
  ntac 2 (pop_assum (CHANGED_TAC o SUBST1_TAC)) >> ntac 2 (pop_assum mp_tac) >>
  pop_assum mp_tac >> simp[AND_IMP_INTRO, GSYM CONJ_ASSOC] >>
  map_every qid_spec_tac [`acc`, ‘err’, `i2`,`i`, `l`] >>
  Induct >- simp[Once peg_eval_cases, mk_linfix_def, PULL_EXISTS] >>
  simp[Once peg_eval_cases] >>
  simp[peg_eval_seq_SOME, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
       GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_FORALL_IMP_THM] >>
  qx_genl_tac[‘i’, ‘i1'’, ‘err’, ‘acc’, ‘eo0’, ‘i3'’, ‘i2'’, ‘sep_r’, ‘sym_r’,
              ‘e01’] >>
  strip_tac >>
  `LENGTH i1 < LENGTH i0` by metis_tac[not_peg0_LENGTH_decreases] >>
  `LENGTH i1' < LENGTH i0` by decide_tac >>
  first_assum (qpat_assum ‘peg_eval _ (i1',sepsym) _’ o
               mp_then (Pos last) mp_tac) >>
  rpt kill_asm_guard >>
  disch_then (qxchl [`sep_pt`] strip_assume_tac) >> rveq >>
  `LENGTH i2' ≤ LENGTH i1'`
    by metis_tac[peg_eval_suffix',
                 DECIDE``x:num ≤ y ⇔ x = y ∨ x < y``] >>
  `LENGTH i2' < LENGTH i0` by decide_tac >>
  first_x_assum (qpat_assum ‘peg_eval _ (i2',sym) _’ o
                 mp_then (Pos last) mp_tac) >>
  rpt kill_asm_guard >>
  disch_then (qxchl [`sym_pt`] strip_assume_tac) >> rveq >>
  simp[mk_linfix_def] >>
  `LENGTH i3' < LENGTH i2'` by metis_tac[not_peg0_LENGTH_decreases] >>
  `LENGTH i3' ≤ LENGTH i1` by decide_tac >>
  first_x_assum (qspecl_then [`i`, `i3'`, ‘err’,
                              `[mkNd UpperN acc; sep_pt; sym_pt]`]
                             mp_tac) >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  `[NT UpperN; ptree_head sep_pt; ptree_head sym_pt] ∈ cmlG.rules ' UpperN`
    by fs[SUBSET_DEF] >>
  simp[]
QED

Theorem length_no_greater:
   peg_eval G (i0, sym) (Success i r eo) ⇒ LENGTH i ≤ LENGTH i0
Proof
  metis_tac[peg_eval_suffix',
            DECIDE ``x ≤ y:num ⇔ x < y ∨ x = y``]
QED

Theorem MAP_TK_11[simp]:
   MAP TK x = MAP TK y ⇔ x = y
Proof
  eq_tac >> simp[] >> strip_tac >>
  match_mp_tac
    (INST_TYPE [beta |-> ``:(token,MMLnonT) grammar$symbol``]
               listTheory.INJ_MAP_EQ) >>
  qexists_tac `TK` >>
  simp[INJ_DEF]
QED

Theorem peg_eval_nTyOp_wrongtok:
   FST tk = LparT ⇒
   ¬peg_eval cmlPEG (tk::i, nt (mkNT nTyOp) f) (Success i' r eo)
Proof
  simp[Once peg_eval_cases, cmlpeg_rules_applied, FDOM_cmlPEG, PULL_EXISTS] >>
  simp[Once peg_eval_cases, cmlpeg_rules_applied, FDOM_cmlPEG, PULL_EXISTS] >>
  rw[] >> gs[]
QED

Theorem peg_EbaseParen_sound:
   ∀i0 i pts eo.
      peg_eval cmlPEG (i0, peg_EbaseParen) (Success i pts eo) ⇒
      (∀i0' N i pts eo.
        LENGTH i0' < LENGTH i0 ∧
        peg_eval cmlPEG (i0', nt (mkNT N) I) (Success i pts eo) ⇒
        ∃pt.
           pts = [pt] ∧ ptree_head pt = NT (mkNT N) ∧
           valid_lptree cmlG pt ∧
           MAP (TOK ## I) i0' = real_fringe pt ++ MAP (TOK ## I) i) ⇒
      ∃pt.
        pts = [pt] ∧ ptree_head pt = NT (mkNT nEbase) ∧
        valid_lptree cmlG pt ∧
        MAP (TOK ## I) i0 = real_fringe pt ++ MAP (TOK ## I) i
Proof
  rw[peg_EbaseParen_def] >> gs[]
  >- (first_x_assum $ drule_at (Pos last) >>
      simp[PULL_EXISTS, peg_EbaseParenFn_def, cmlG_FDOM, cmlG_applied,
           DISJ_IMP_THM, pairTheory.PAIR_MAP])
  >- (first_assum (qpat_assum ‘peg_eval _ (_, nt (mkNT nE) I) _’ o
                   mp_then (Pos last) mp_tac) >> impl_tac >- simp[] >>
      disch_then $ qx_choose_then ‘pt1’ strip_assume_tac >> gvs[] >>
      first_x_assum (qpat_assum ‘peg_eval _ (_, nt (mkNT nElist1) I) _’ o
                     mp_then (Pos last) mp_tac) >> simp[] >>
      qpat_assum ‘peg_eval _ (_, nt (mkNT nE) I) _’ $
                 mp_then (Pos hd) mp_tac length_no_greater >> rw[] >>
      simp[peg_EbaseParenFn_def, cmlG_applied, cmlG_FDOM,
           DISJ_IMP_THM, FORALL_AND_THM, pairTheory.PAIR_MAP]) >>
  first_assum (qpat_assum ‘peg_eval _ (_, nt (mkNT nE) I) _’ o
               mp_then (Pos last) mp_tac) >> impl_tac >- simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum (qpat_assum ‘peg_eval _ (_, nt (mkNT nEseq) I) _’ o
                 mp_then (Pos last) mp_tac) >> impl_tac
  >- (qpat_assum ‘peg_eval _ (_, nt (mkNT nE) I) _’ $
      mp_then (Pos hd) mp_tac length_no_greater >> simp[]) >>
  rw[] >>
  simp[peg_EbaseParenFn_def, cmlG_applied, cmlG_FDOM,
       DISJ_IMP_THM, FORALL_AND_THM, pairTheory.PAIR_MAP]
QED

Theorem PAIR_MAP_I[local,simp]:
  (f ## I) x = (f (FST x), SND x) ⇔ T
Proof simp[PAIR_MAP]
QED

Theorem bindNT0_lemma[local,simp] = REWRITE_RULE [GSYM mkNd_def] bindNT0_def

(* left recursive rules in the grammar turn into calls to rpt in the PEG,
   and this in turn requires inductions *)
Theorem ptPapply_lemma:
   ∀limit.
     (∀i0 i pts eo.
       LENGTH i0 < limit ⇒
       peg_eval cmlPEG (i0, nt (mkNT nPbase) I) (Success i pts eo) ⇒
       ∃pt. pts = [pt] ∧ ptree_head pt = NN nPbase ∧ valid_lptree cmlG pt ∧
            MAP (TK ## I) i0 = real_fringe pt ++ MAP (TK ## I) i) ⇒
     ∀ptlist pt0 acc i0 err.
       peg_eval_list cmlPEG (i0, nt (mkNT nPbase) I) (i, ptlist, err) ∧
       ptree_head pt0 = NN nPbase ∧ valid_lptree cmlG pt0 ∧
       ptree_head acc = NN nPConApp ∧ valid_lptree cmlG acc ∧
       LENGTH i0 < limit ⇒
       ∃pt. ptPapply0 acc (pt0 :: FLAT ptlist) = [pt] ∧
            ptree_head pt = NN nPapp ∧ valid_lptree cmlG pt ∧
            real_fringe acc ++ real_fringe pt0 ++ MAP (TK ## I) i0 =
            real_fringe pt ++ MAP (TK ## I) i
Proof
  gen_tac >> strip_tac >> Induct
  >- (simp[Once peg_eval_list] >> simp[ptPapply0_def] >>
      dsimp[cmlG_FDOM, cmlG_applied]) >>
  dsimp[Once peg_eval_list] >> rpt strip_tac >>
  first_x_assum $ drule_all >> strip_tac >> rveq >> simp[ptPapply0_def] >>
  drule_at (Pos last) not_peg0_LENGTH_decreases >> impl_tac >- simp[] >>
  strip_tac >>
  rename [‘peg_eval _ (i0, _) (Sucess i1 [pt1] eo1)’,
          ‘peg_eval_list _ (i1, _) (i, ptlist,err)’] >>
  first_x_assum $
    qspecl_then [‘pt1’, ‘mkNd (mkNT nPConApp) [acc; pt0]’, ‘i1’, ‘err’] mp_tac>>
  simp[] >>
  disch_then irule >> dsimp[cmlG_applied, cmlG_FDOM]
QED

val pmap_cases =
  rpt ((rename [‘(_,_) = (_ ## _) pair’] >> Cases_on ‘pair’ >> fs[] >> rveq)
         ORELSE
       (rename [‘(_ ## _) pair = (_,_)’] >> Cases_on ‘pair’ >> fs[] >> rveq))

Theorem pmap_EQ_pair[simp,local]:
  (f ## g) p = (a,b) ⇔ ∃c d. p = (c,d) ∧ f c = a ∧ g d = b
Proof
  Cases_on ‘p’ >> simp[]
QED

Theorem pair_EQ_components[simp,local]:
  (p = (x,SND p) ⇔ FST p = x) ∧
  ((x,SND p) = p ⇔ FST p = x) ∧
  (p = (FST p,y) ⇔ SND p = y) ∧
  ((FST p,y) = p ⇔ SND p = y)
Proof
  Cases_on ‘p’ >> simp[EQ_SYM_EQ]
QED

Theorem peg_sound:
   ∀N i0 i pts eo.
       peg_eval cmlPEG (i0,nt N I) (Success i pts eo) ⇒
       ∃pt. pts = [pt] ∧ ptree_head pt = NT N ∧
            valid_lptree cmlG pt ∧
            MAP (TOK ## I) i0 = real_fringe pt ++ MAP (TOK ## I) i
Proof
  ntac 2 gen_tac >> ‘∃iN. iN = (i0,N)’ by simp[] >> pop_assum mp_tac >>
  map_every qid_spec_tac [‘i0’, ‘N’, ‘iN’] >>
  qspec_then `measure (LENGTH:(token # locs) list->num) LEX measure NT_rank`
             (ho_match_mp_tac o
              SIMP_RULE (srw_ss()) [pairTheory.WF_LEX,
                                    prim_recTheory.WF_measure])
             relationTheory.WF_INDUCTION_THM >>
  dsimp[pairTheory.LEX_DEF] >>
  qx_genl_tac [`N`, `i0`, `i`, `pts`, ‘eo’] >> strip_tac >>
  simp[peg_eval_NT_SOME, cmlPEGTheory.FDOM_cmlPEG] >>
  disch_then (CONJUNCTS_THEN2 strip_assume_tac mp_tac) >> rveq >>
  simp[cmlPEGTheory.cmlpeg_rules_applied, ptree_list_loc_def]
  >- (print_tac "nNonETopLevelDecs" >>
      `NT_rank (mkNT nDecl) < NT_rank (mkNT nNonETopLevelDecs)`
        by simp[NT_rank_def] >>
      strip_tac >> rveq >> dsimp[cmlG_FDOM, cmlG_applied]
      >- (first_x_assum (drule_all_then strip_assume_tac) >> rveq >> csimp[] >>
          rename1
           `peg_eval _ (inp0, nt (mkNT nDecl) _) (Success inp1 _ _)` >>
          `LENGTH inp1 < LENGTH inp0`
            by metis_tac[not_peg0_LENGTH_decreases, peg0_nDecl] >>
          csimp[PULL_EXISTS] >> metis_tac[])
      >- (fs[] >> csimp[] >> metis_tac[DECIDE ``x < SUC x``])
      >- (csimp[] >> fs[] >> metis_tac[DECIDE ``x < SUC x``]))
  >- (print_tac "nTopLevelDecs" >> simp[] >>
      `NT_rank (mkNT nE) < NT_rank (mkNT nTopLevelDecs) ∧
       NT_rank (mkNT nDecl) < NT_rank (mkNT nTopLevelDecs)`
          by simp[NT_rank_def] >>
      strip_tac >> rveq >> simp[cmlG_FDOM, cmlG_applied]
      >- (dsimp[APPEND_EQ_CONS] >> csimp[] >>
          first_x_assum (drule_all_then strip_assume_tac) >> rveq >> simp[] >>
          rename1 `peg_eval _ (inp0, _) (Success (h::inp1) [_] _)` >>
          `LENGTH (h :: inp1) < LENGTH inp0`
            by metis_tac[not_peg0_LENGTH_decreases, peg0_nE] >>
          fs[SF SFY_ss])
      >- (first_x_assum (drule_all_then strip_assume_tac) >> rveq >> dsimp[] >>
          csimp[] >>
          rename1
            `peg_eval _ (inp0, nt (mkNT nDecl) I) (Success inp1 _ _)` >>
          `LENGTH inp1 < LENGTH inp0` suffices_by metis_tac[] >>
          metis_tac[not_peg0_LENGTH_decreases, peg0_nDecl])
      >- (dsimp[] >> csimp[] >> fs[GSYM CONJ_ASSOC, SF SFY_ss])
      >- (dsimp[] >> csimp[] >> fs[GSYM CONJ_ASSOC, SF SFY_ss])
      >- (first_x_assum
          (qpat_assum ‘peg_eval _ (_, nt (mkNT nDecl) I) _’ o
           mp_then (Pos last) mp_tac) >>
          simp[] >> strip_tac >> rveq >> dsimp[] >> csimp[] >>
          simp[GSYM CONJ_ASSOC] >> first_x_assum irule >>
          metis_tac[not_peg0_LENGTH_decreases, peg0_nDecl])
      >- (dsimp[] >> csimp[] >> fs[GSYM CONJ_ASSOC, SF SFY_ss])
      >- (dsimp[] >> csimp[] >> fs[GSYM CONJ_ASSOC, SF SFY_ss])
      >- (first_x_assum $
            qpat_assum ‘peg_eval _ (_, nt (mkNT nDecl) I) _’ o
            mp_then (Pos last) mp_tac >>
          simp[] >> strip_tac >> rveq >> dsimp[] >> csimp[GSYM CONJ_ASSOC] >>
          first_x_assum irule >>
          metis_tac[not_peg0_LENGTH_decreases, peg0_nDecl])
      >- (dsimp[] >> csimp[] >> fs[GSYM CONJ_ASSOC, SF SFY_ss])
      >- (dsimp[] >> csimp[] >> fs[GSYM CONJ_ASSOC, SF SFY_ss]))
  (* >- (print_tac "nREPLTop">>
      `NT_rank (mkNT nE) < NT_rank (mkNT nREPLTop) ∧
       NT_rank (mkNT nTopLevelDec) < NT_rank (mkNT nREPLTop)`
          by simp[NT_rank_def] >>
      strip_tac >> rveq >> simp[] >>
      first_x_assum (erule strip_assume_tac) >> rveq >>
      dsimp[cmlG_applied, cmlG_FDOM]) *)
  (*>- (print_tac "nREPLPhrase" >>
      `NT_rank (mkNT nE) < NT_rank (mkNT nREPLPhrase) ∧
       NT_rank (mkNT nTopLevelDecs) < NT_rank (mkNT nREPLPhrase)`
          by simp[NT_rank_def] >>
      strip_tac >> rveq >> simp[] >>
      first_x_assum (erule strip_assume_tac) >> rveq >>
      dsimp[cmlG_applied, cmlG_FDOM]) *)
  >- (print_tac "nStructure" >> rpt strip_tac >> rveq >>
      simp[DISJ_IMP_THM, FORALL_AND_THM, cmlG_FDOM, cmlG_applied] >>
      loseC ``NT_rank`` >> fs[] >>
      rename [
        ‘peg_eval cmlPEG (vi, nt (mkNT nStructName) I) (Success opti vt _)’] >>
      `LENGTH vi < SUC (LENGTH vi)` by decide_tac >>
      first_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      `LENGTH opti < LENGTH vi`
        by metis_tac[not_peg0_LENGTH_decreases, peg0_nStructName] >>
      `LENGTH opti < SUC (LENGTH vi)` by decide_tac >>
      first_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      rename[
        ‘peg_eval cmlPEG (opti, OPTSIG) (Success (eqT::strT::di)[opt] _)’] >>
      `LENGTH (eqT::strT::di) ≤ LENGTH opti`
        by metis_tac[peg_eval_suffix',
                     DECIDE``x:num ≤ y ⇔ x < y ∨ x = y``] >> fs[] >>
      `LENGTH di < SUC (LENGTH vi)` by decide_tac >>
      first_x_assum (drule_all_then strip_assume_tac) >> rveq >> simp[] >>
      gs[])
  >- (print_tac "nStructName" >> simp[peg_StructName_def] >>
      dsimp[cmlG_applied, cmlG_FDOM, PAIR_MAP])
  >- (print_tac "nOptionalSignatureAscription" >> rpt strip_tac >> rveq >>
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
             by simp[NT_rank_def] >> first_x_assum drule_all >>
          rename[‘peg_eval _ (i0, nt (mkNT nSpecLine) I) (Success i1 r _)’]>>
          `LENGTH i1 < LENGTH i0`
            by metis_tac[not_peg0_LENGTH_decreases, peg0_nSpecLine] >>
          first_x_assum $ drule_all >> rpt strip_tac >> rveq >> fs[])
      >- (dsimp[MAP_EQ_SING] >> csimp[]>>fs[] >> metis_tac[DECIDE``x < SUC x``])
      >> fs[cmlG_FDOM, cmlG_applied, MAP_EQ_SING] >> dsimp[] >> csimp[] >>
      metis_tac[DECIDE``x< SUC x``])
  >- (print_tac "nSpecLine" >> strip_tac >> rveq >>
      fs[cmlG_applied, cmlG_FDOM, peg_eval_TypeDec_wrongtok] >> gvs[]
      >- (rename [‘
            peg_eval _ (i1, nt (mkNT nV) I) (Success ((ColonT,_)::i2) r _)’] >>
          first_assum (resolve_then Any (drule_then strip_assume_tac)
                       $ DECIDE “x < SUC x”) >>
          gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
          drule_then assume_tac (MATCH_MP not_peg0_LENGTH_decreases peg0_nV) >>
          gvs[] >>
          `LENGTH i2 < SUC(LENGTH i1)` by decide_tac >>
          first_x_assum (drule_all_then strip_assume_tac) >> rveq >> dsimp[])
      >- (rename[‘peg_eval _ (i1, nt (mkNT nTypeName) I)(Success i2 nmpts _)’]>>
          first_assum (qpat_assum ‘peg_eval _ (_, nt (mkNT nTypeName) I) _’ o
                       mp_then (Pos last) mp_tac) >>
          simp_tac (srw_ss()) [] >> ASM_REWRITE_TAC [] >>
          disch_then (qx_choose_then `nmpt` strip_assume_tac) >>
          dsimp[MAP_EQ_SING] >> csimp[GSYM CONJ_ASSOC] >> first_x_assum irule >>
          metis_tac[not_peg0_LENGTH_decreases, peg0_nTypeName,
                    DECIDE “x < y ⇒ x < SUC y”])
      >- (dsimp[MAP_EQ_SING] >> csimp[] >> metis_tac[DECIDE``x<SUC x``])>>
      `NT_rank (mkNT nTypeDec) < NT_rank (mkNT nSpecLine)`
         by simp[NT_rank_def] >>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[])
  >- (print_tac "nOptTypEqn" >> strip_tac >> rveq >>
      simp[cmlG_FDOM, cmlG_applied] >> dsimp[MAP_EQ_SING] >> csimp[] >>
      fs[] >> metis_tac[DECIDE ``x < SUC x``])
  >- (print_tac "nDecls" >>
      `NT_rank (mkNT nDecl) < NT_rank (mkNT nDecls)`
        by simp[NT_rank_def] >>
      strip_tac >> rveq >> fs[cmlG_applied, cmlG_FDOM]
      >- (first_x_assum (drule_all_then strip_assume_tac) >>
          first_x_assum (resolve_then Any (drule_at (Pos (el 2)))
                         not_peg0_LENGTH_decreases)>> simp[] >>
          disch_then drule >> simp[PULL_EXISTS, DISJ_IMP_THM, FORALL_AND_THM])
      >- (dsimp[MAP_EQ_SING] >> csimp[] >> metis_tac[DECIDE``x<SUC x``]) >>
      dsimp[MAP_EQ_SING] >> csimp[] >> metis_tac[DECIDE``x<SUC x``])
  >- (print_tac "nTypeAbbrevDec" >>
      rpt strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM] >>
      dsimp[listTheory.APPEND_EQ_CONS, MAP_EQ_SING] >> csimp[] >> gvs[] >>
      first_assum (resolve_then Any drule (DECIDE “x < SUC x”)) >> strip_tac >>
      gvs[] >>
      rename[
          ‘peg_eval _ (inp, nt(mkNT nTypeName) _) (Success (eqT::inp1) _ _)’,
          ‘peg_eval _ (inp1, nt(mkNT nType) I) (Success inp2 t2 _)’
        ] >>
      `LENGTH (eqT::inp1) < LENGTH inp`
        by metis_tac[not_peg0_LENGTH_decreases, peg0_nTypeName] >> fs[] >>
      `LENGTH inp1 < SUC (LENGTH inp)` by simp[] >>
      first_x_assum $ drule_all >>
      simp[] >> metis_tac[])
  >- (print_tac "nDecl" >> simp[PULL_EXISTS, EXISTS_PROD] >>
      rpt strip_tac >>
      gvs[peg_eval_TypeDec_wrongtok, peg_eval_TypeAbbrevDec_wrongtok,
          peg_eval_Structure_wrongtok] >>
      dsimp[cmlG_applied, cmlG_FDOM, APPEND_EQ_CONS, MAP_EQ_CONS]>>
      csimp[] (* 7 *)
      >- (rename [‘peg_eval cmlPEG (i1, nt (mkNT nPattern) I) _’] >>
          ‘LENGTH i1 < SUC (LENGTH i1)’ by decide_tac >>
          first_assum (drule_all_then strip_assume_tac) >> rveq >> simp[] >>
          first_x_assum irule >> simp[SF SFY_ss] >>
          rpt (dxrule peg_eval_suffix') >> rw[] >> rw[])
      >- simp[GSYM CONJ_ASSOC, SF SFY_ss]
      >- simp[GSYM CONJ_ASSOC, SF SFY_ss]
      >- (first_assum $
            resolve_then Any (drule_then strip_assume_tac) $
            DECIDE “x < SUC x” >> gvs[] >>
          simp[PULL_EXISTS, MAP_EQ_APPEND] >> rw[] >>
          first_x_assum
            (qpat_x_assum ‘peg_eval _ _ (Success((EndT,_)::_) _ _)’ o
             mp_then (Pos last) mp_tac) >>
          gvs[PULL_EXISTS, MAP_EQ_APPEND, FORALL_PROD])
      >- (`NT_rank (mkNT nTypeDec) < NT_rank (mkNT nDecl)`
            by simp[NT_rank_def] >>
          first_x_assum (drule_all_then strip_assume_tac) >>
          dsimp[cmlG_FDOM, cmlG_applied])
      >- (`NT_rank (mkNT nTypeAbbrevDec) < NT_rank (mkNT nDecl)`
            by simp[NT_rank_def] >>
          first_x_assum (erule strip_assume_tac) >>
          dsimp[cmlG_FDOM, cmlG_applied])
      >- (‘NT_rank (mkNT nStructure) < NT_rank (mkNT nDecl)’
            by simp[NT_rank_def] >>
          first_x_assum $ drule_all_then strip_assume_tac >>
          simp[]))
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
      rpt strip_tac >> rveq >> simp[cmlG_FDOM, cmlG_applied, MAP_EQ_SING] >>
      fs[]
      >- (dsimp[listTheory.APPEND_EQ_CONS, MAP_EQ_SING] >> csimp[] >>
          rename[‘peg_eval _ (i1,nt (mkNT nPattern) I)
                    (Success((EqualsT,ll)::i2) r _)’] >>
          `LENGTH i1 < SUC (LENGTH i1)` by decide_tac >>
          first_assum (erule strip_assume_tac) >> rveq >> simp[] >>
          `LENGTH ((EqualsT,ll)::i2) ≤ LENGTH i1`
            by metis_tac[peg_eval_suffix',
                         DECIDE``x≤y ⇔ x = y ∨ x < y:num``] >> fs[]>>
          `LENGTH i2 < SUC (LENGTH i1)` by decide_tac >>
          metis_tac[]) >>
      dsimp[] >> csimp[] >> metis_tac[DECIDE``x<SUC x``])
  >- (print_tac "nPtuple" >> strip_tac >> rveq >>
      dsimp[cmlG_applied, cmlG_FDOM] >>
      first_x_assum $ drule_at (Pos last) >>
      simp[] >> strip_tac >> rveq >> simp[])
  >- (print_tac "nPatternList" >> strip_tac >> rveq >>
      simp[cmlG_FDOM, cmlG_applied] >>
      `NT_rank (mkNT nPattern) < NT_rank (mkNT nPatternList)`
        by simp[NT_rank_def] >>
      first_x_assum (erule mp_tac) >> strip_tac >> rveq >> simp[] >>
      imp_res_tac length_no_greater >> fs[] >>
      fs[MAP_EQ_APPEND, MAP_EQ_CONS] >>
      first_x_assum (qpat_assum ‘peg_eval _ (_, nt (mkNT nPatternList) I) _’ o
                     mp_then (Pos last) mp_tac) >>
      simp[] >> strip_tac >> rveq >> dsimp[] >> rfs[PAIR_MAP])
  >- (
      print_tac "nPattern" >> strip_tac >> rveq >>
      `NT_rank (mkNT nPas) < NT_rank (mkNT nPattern)` by simp[NT_rank_def] >>
      simp[cmlG_FDOM, cmlG_applied]
      >- (
          dsimp[APPEND_EQ_CONS] >> csimp[] >>
          first_x_assum (erule mp_tac) >> strip_tac >> rveq >> simp[] >>
          fs[MAP_EQ_APPEND] >> rveq >> dsimp[] >> fs[] >>
          rename1`peg_eval _ (inp2, nt (mkNT nType) I)` >>
          first_x_assum (qspecl_then [`mkNT nType`, `inp2`] mp_tac) >>
          imp_res_tac length_no_greater \\ fs[] >>
          simp[] >> metis_tac[])
      >- (dsimp[MAP_EQ_CONS] >> disj1_tac >>
          first_x_assum (erule mp_tac) >> strip_tac >> rveq >> simp[])
      >- (first_x_assum $
            drule_all_then $ qx_choose_then ‘pcpt’ strip_assume_tac >>
          simp[DISJ_IMP_THM, PULL_EXISTS, SF CONJ_ss, GSYM CONJ_ASSOC] >>
          first_x_assum irule >> simp[SF SFY_ss] >>
          rpt (dxrule length_no_greater) >> simp[]))
  >- (
      print_tac "nPas" >>
      `NT_rank (mkNT nPcons) < NT_rank (mkNT nPas)`
        by simp[NT_rank_def] >> strip_tac >> rveq >>
      simp[cmlG_applied, cmlG_FDOM]
      >- (imp_res_tac length_no_greater
          \\ gs [GSYM LESS_EQ]
          \\ first_x_assum (drule_all_then strip_assume_tac)
          \\ gvs [MAP_EQ_CONS, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS]
          \\ csimp [] \\ simp [GSYM CONJ_ASSOC]
          \\ ‘NT_rank (mkNT nV) < NT_rank (mkNT nPas)’
            by simp [NT_rank_def]
          \\ first_x_assum $ drule_all_then strip_assume_tac
          \\ simp [])
      >- (first_x_assum $ drule_all_then strip_assume_tac >> gvs[]) >>
      first_x_assum $ drule_all_then strip_assume_tac >> gvs[])
  >- (print_tac "nPcons" >>
      `NT_rank (mkNT nPapp) < NT_rank (mkNT nPcons)`
        by simp[NT_rank_def] >> strip_tac >> rveq >>
      simp[cmlG_applied, cmlG_FDOM]
      >- (first_x_assum $ drule_all_then strip_assume_tac >>
          gvs[MAP_EQ_CONS, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
          csimp[] >> simp[GSYM CONJ_ASSOC] >> first_x_assum irule >>
          simp[SF SFY_ss] >> rpt (dxrule length_no_greater) >> simp[])
      >- (first_x_assum $ drule_all_then strip_assume_tac >> gvs[]) >>
      first_x_assum $ drule_all_then strip_assume_tac >> gvs[] >>
      simp[PULL_EXISTS, DISJ_IMP_THM, SF CONJ_ss, GSYM CONJ_ASSOC] >>
      first_x_assum irule >> simp[SF SFY_ss] >>
      rpt (dxrule length_no_greater) >> simp[])
  >- (print_tac "nPapp" >>
      `NT_rank (mkNT nConstructorName) < NT_rank (mkNT nPapp) ∧
       NT_rank (mkNT nPbase) < NT_rank (mkNT nPapp)`
        by simp[NT_rank_def] >>
      reverse strip_tac >> rveq >> simp[cmlG_FDOM, cmlG_applied]
      >- (first_x_assum (erule mp_tac) >> strip_tac >> rveq >> dsimp[] >>
          fs[]) >>
      first_x_assum (erule mp_tac) >> strip_tac >> rveq >> dsimp[] >>
      imp_res_tac
        (MATCH_MP not_peg0_LENGTH_decreases peg0_nConstructorName) >>
      fs[peg_eval_rpt, Once peg_eval_list]
      >- simp[cmlG_FDOM, cmlG_applied] >>
      first_assum (erule mp_tac) >> strip_tac >> rveq >> dsimp[] >>
      simp[ptPapply_def] >>
      first_assum (mp_then (Pos (el 2)) mp_tac ptPapply_lemma) >>
      ntac 2 (disch_then (first_assum o mp_then (Pos (el 2)) mp_tac)) >>
      rename [‘peg_eval _ (i0, nt (mkNT nConstructorName) I)’] >>
      disch_then (qspec_then ‘LENGTH i0’ mp_tac) >> simp[] >>
      rename [‘mkNd (mkNT nPConApp) [pt]’] >>
      disch_then (qspec_then ‘mkNd (mkNT nPConApp) [pt]’ mp_tac) >>
      simp[cmlG_applied, cmlG_FDOM] >> disch_then irule >>
      imp_res_tac (MATCH_MP not_peg0_LENGTH_decreases peg0_nPbase) >>
      simp[SF SFY_ss])
  >- (print_tac "nPbase" >>
      `NT_rank (mkNT nV) < NT_rank (mkNT nPbase) ∧
       NT_rank (mkNT nConstructorName) < NT_rank (mkNT nPbase) ∧
       NT_rank (mkNT nPtuple) < NT_rank (mkNT nPbase)`
         by simp[NT_rank_def] >>
      strip_tac >> rveq
      >- (first_x_assum (erule mp_tac) >> strip_tac >> rveq >>
          dsimp[cmlG_applied, cmlG_FDOM])
      >- (first_x_assum (erule mp_tac) >> strip_tac >> rveq >>
          dsimp[cmlG_applied, cmlG_FDOM])
      >- (simp[cmlG_FDOM, cmlG_applied] >> rename[‘isInt h’] >>
          Cases_on `h` >> fs[])
      >- (simp[cmlG_FDOM, cmlG_applied] >> asm_match `isString h` >>
          Cases_on `h` >> fs[])
      >- (simp[cmlG_FDOM, cmlG_applied] >> asm_match `isCharT h` >>
          Cases_on `h` >> fs[])
      >- (first_x_assum (erule mp_tac) >> strip_tac >> rveq >>
          dsimp[cmlG_applied, cmlG_FDOM])
      >- simp[cmlG_FDOM, cmlG_applied]
      >- (simp[cmlG_FDOM, cmlG_applied] >>
          first_x_assum $ drule_at (Pos last) >> kill_asm_guard >>
          ASM_REWRITE_TAC [] >> strip_tac >> rveq >> dsimp[])
      >- dsimp[cmlG_applied, cmlG_FDOM]
      >- (simp[cmlG_FDOM, cmlG_applied] >>
          dsimp[] >> csimp[] >> fs[] >> simp[GSYM CONJ_ASSOC, SF SFY_ss])
      >- (fs[] >> rveq >> fs[])
      >- (fs[] >> rveq >> fs[]))
  >- (print_tac "nConstructorName" >>
      simp[pairTheory.EXISTS_PROD] >>
      `NT_rank (mkNT nUQConstructorName) < NT_rank (mkNT nConstructorName)`
        by simp[NT_rank_def] >>
      strip_tac >> rveq >> simp[]
      >- (first_x_assum (erule strip_assume_tac) >> rveq >>
          simp[cmlG_applied, cmlG_FDOM] >> NO_TAC) >>
      simp[cmlG_FDOM, cmlG_applied] >>
      asm_match `destLongidT t = SOME(m,v)` >> Cases_on `t` >> fs[])
  >- (print_tac "nUQConstructorName" >>
      simp[peg_UQConstructorName_def] >>
      dsimp[cmlG_applied, cmlG_FDOM, FORALL_PROD])
  >- (print_tac "nDconstructor" >>
      `NT_rank (mkNT nUQConstructorName) < NT_rank (mkNT nDconstructor)`
        by simp[NT_rank_def] >>
      strip_tac >>
      rveq >> simp[cmlG_FDOM, cmlG_applied, listTheory.APPEND_EQ_CONS,
                   MAP_EQ_SING] >>
      first_x_assum (qpat_x_assum ‘NT_rank _ < NT_rank _’ o
                     mp_then (Pos hd) mp_tac) >>
      disch_then (first_assum o
                  mp_then (Pos hd) strip_assume_tac) >>
      simp[] >> rveq >> dsimp[] >> csimp[] >>
      first_x_assum (qpat_assum ‘peg_eval _ (_, nt (mkNT nTbaseList) I) _’o
                     mp_then Any mp_tac) >>
      metis_tac[not_peg0_LENGTH_decreases, peg0_nUQConstructorName,
                LENGTH, DECIDE``SUC x < y ⇒ x < y``, MAP])
  >- (print_tac "nDtypeDecl" >>
      `NT_rank (mkNT nTypeName) < NT_rank (mkNT nDtypeDecl)`
        by simp[NT_rank_def] >>
      strip_tac >> rveq >>
      dsimp[cmlG_applied, cmlG_FDOM, listTheory.APPEND_EQ_CONS, MAP_EQ_SING] >>
      csimp[] >>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >> csimp[] >>
      first_x_assum (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[DISJ_IMP_THM, FORALL_AND_THM, peg_eval_tok_SOME, pegsym_to_sym_def,
           mktokLf_def, cmlG_applied, cmlG_FDOM, SUBSET_DEF] >>
      (peg0_nTypeName |> Q.INST[`f` |-> `I`] |> assume_tac) >>
      erule mp_tac (GEN_ALL not_peg0_LENGTH_decreases)>>
      simp[] >> rw[SF SFY_ss])
  >- (print_tac "nTypeDec" >> simp[peg_TypeDec_def] >> strip_tac >> rveq >>
      dsimp[cmlG_FDOM, cmlG_applied, mktokLf_def, MAP_EQ_SING] >> csimp[] >>
      fs[] >> pop_assum (mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[pegsym_to_sym_def, cmlG_applied, cmlG_FDOM, SUBSET_DEF,
           DISJ_IMP_THM, FORALL_AND_THM, EXISTS_PROD] >>
      dsimp[ptree_list_loc_def, SF SFY_ss])
  >- (print_tac "nTyVarList" >> strip_tac >>
      `NT_rank (mkNT nTyvarN) < NT_rank (mkNT nTyVarList)`
        by simp[NT_rank_def] >>
      first_x_assum (mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[DISJ_IMP_THM, pegsym_to_sym_def, cmlG_FDOM, cmlG_applied,
           SUBSET_DEF, FORALL_AND_THM, mktokLf_def] >> dsimp[SF SFY_ss])
  >- (print_tac "nTypeName" >>
      simp[] >> strip_tac >> rveq >>
      dsimp[cmlG_FDOM, cmlG_applied, MAP_EQ_SING]
      >- (first_x_assum (first_assum o mp_then (Pos last) mp_tac) >>
          simp[NT_rank_def] >> strip_tac >> rveq >> dsimp[])
      >- (simp[listTheory.APPEND_EQ_CONS] >> dsimp[MAP_EQ_CONS] >>
          csimp[] >>
          first_assum (qpat_assum ‘peg_eval _ (_, nt (mkNT nTyVarList) I) _’ o
                       mp_then (Pos last) mp_tac) >> impl_tac >- simp[] >>
          disch_then (qxchl [`tyvl_pt`] strip_assume_tac) >>
          rveq >> simp[] >>
          qpat_x_assum ‘peg_eval _ (_, nt (mkNT nTyVarList) I) _’ $
                       mp_then (Pos hd) assume_tac length_no_greater >>
          fs[SF SFY_ss])
      >- (first_x_assum (first_assum o mp_then (Pos last) mp_tac) >>
          simp[] >> strip_tac >> rveq >> simp[] >> rename1 `isTyvarT HH` >>
          Cases_on `HH` >> fs[])
      >- gvs[]
      >- gvs[] >>
      gvs [])
  >- (print_tac "nPType" >>
      `NT_rank (mkNT nDType) < NT_rank (mkNT nPType)` by simp[NT_rank_def] >>
      strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM]
      >- (first_x_assum (erule mp_tac) >>
          simp[MAP_EQ_APPEND, MAP_EQ_CONS] >>
          strip_tac >> rveq >>
          first_x_assum (qpat_assum ‘peg_eval _ (_, nt (mkNT nPType) I) _’ o
                         mp_then (Pos last) mp_tac) >>
          simp[] >> strip_tac >> rveq >>
          fs[MAP_EQ_APPEND, MAP_EQ_CONS] >>
          dsimp[] >> metis_tac[])
      >- (first_x_assum (erule mp_tac) >> strip_tac >> rveq >> simp[]) >>
      first_x_assum (erule mp_tac) >> strip_tac >> rveq >> simp[])
  >- (print_tac "nUQTyOp" >>
      dsimp[cmlG_FDOM, cmlG_applied, EXISTS_PROD, FORALL_PROD] >>
      qx_gen_tac `h` >> Cases_on `h` >> simp[])
  >- (print_tac "nTyOp" >> strip_tac >> rveq >>
      dsimp[cmlG_applied, cmlG_FDOM, MAP_EQ_SING]
      >- (first_x_assum $ drule_at (Pos last) >>
          simp[NT_rank_def] >> strip_tac >> rveq >> simp[])
      >- (rename [`isLongidT h`] >> Cases_on `h` >> fs[]))
  >- (print_tac "nTbaseList" >> strip_tac >> rveq >>
      dsimp[cmlG_FDOM, cmlG_applied] >>
      ‘NT_rank (mkNT nPTbase) < NT_rank (mkNT nTbaseList)’
        by simp[NT_rank_def] >>
      first_x_assum (pop_assum o mp_then (Pos hd) mp_tac) >>
      disch_then (first_assum o mp_then (Pos hd) strip_assume_tac) >> rveq >>
      simp[] >> dsimp[] >> csimp[] >>
      metis_tac[not_peg0_LENGTH_decreases, peg0_nPTbase])
  >- (print_tac "nTypeList1" >>
      CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ DNF_ss) [EXISTS_PROD])) >>
      strip_tac >> rveq >>
      dsimp[cmlG_FDOM, cmlG_applied, listTheory.APPEND_EQ_CONS, MAP_EQ_SING] >>
      csimp[] >>
      `NT_rank (mkNT nType) < NT_rank (mkNT nTypeList1)` by simp[NT_rank_def]
      >- (first_x_assum (erule mp_tac) >>
          erule assume_tac
                (length_no_greater |> Q.GEN `sym`
                                   |> Q.ISPEC `nt (mkNT nType) I` |> GEN_ALL) >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          fs[] >> simp[] >> rpt strip_tac >> rveq >> simp[])
      >- (first_x_assum (erule strip_assume_tac) >> rveq >> simp[]) >>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[])
  >- (print_tac "nTypeList2" >>
      CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ DNF_ss) [EXISTS_PROD])) >>
      strip_tac >> rveq >>
      dsimp[cmlG_applied, cmlG_FDOM, listTheory.APPEND_EQ_CONS, MAP_EQ_SING]>>
      csimp[] >>
      `NT_rank (mkNT nType) < NT_rank (mkNT nTypeList2)` by simp[NT_rank_def]>>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
      erule assume_tac
            (length_no_greater |> Q.GEN `sym` |> Q.ISPEC `nt (mkNT nType) I`
                               |> GEN_ALL) >> fs[] >> simp[] >>
      strip_tac >> rveq >> simp[])
  >- (print_tac "nPTbase" >>
      CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ DNF_ss) [EXISTS_PROD])) >>
      strip_tac >> rveq >>
      fs[cmlG_FDOM, cmlG_applied, peg_eval_nTyOp_wrongtok] >>
      rveq >> fs[]
      >- (first_x_assum (first_assum o mp_then Any mp_tac) >> simp[] >>
          strip_tac >> rveq >> dsimp[])
      >- (rename [‘isTyvarT tk’] >> Cases_on ‘tk’ >> fs[])
      >- (‘NT_rank (mkNT nTyOp) < NT_rank (mkNT nPTbase)’ by simp[NT_rank_def]>>
          first_x_assum (pop_assum o mp_then Any mp_tac) >>
          disch_then (first_assum o mp_then (Pos hd) strip_assume_tac) >>
          rveq >> simp[]))
  >- (print_tac "nTbase" >>
      CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ DNF_ss) [EXISTS_PROD])) >>
      strip_tac >> rveq >>
      fs[cmlG_FDOM, cmlG_applied, peg_eval_nTyOp_wrongtok] >>
      rveq >> fs[]
      >- (first_x_assum $ drule_at (Pos last) >> simp[] >> strip_tac >> rveq >>
          dsimp[])
      >- (first_assum (qpat_assum ‘peg_eval _ (_, nt (mkNT nTypeList2) _) _’ o
                       mp_then (Pos last) mp_tac) >>
          rpt kill_asm_guard >> strip_tac >> rveq >> dsimp[] >>
          imp_res_tac length_no_greater >>
          first_x_assum (qpat_assum ‘peg_eval _ (_, nt (mkNT nTyOp) _) _’ o
                         mp_then (Pos last) mp_tac) >>
          fs[] >> simp[] >> strip_tac >> rveq >> dsimp[])
      >- (asm_match `isTyvarT h` >> Cases_on`h` >> fs[])
      >- (`NT_rank (mkNT nTyOp) < NT_rank (mkNT nTbase)` by simp[NT_rank_def] >>
          first_x_assum (erule mp_tac) >> strip_tac >> rveq >> simp[])
      >- (first_assum (qpat_assum ‘peg_eval _ (_, nt (mkNT nTypeList2) _) _’ o
                       mp_then (Pos last) mp_tac) >>
          rpt kill_asm_guard >> strip_tac >> rveq >> simp[] >>
          imp_res_tac length_no_greater >> fs[] >>
          first_x_assum (qpat_assum ‘peg_eval _ (_, nt (mkNT nTyOp) _) _’ o
                         mp_then (Pos last) mp_tac) >>
          simp[] >> strip_tac >> rveq >> dsimp[]) >>
      first_assum (qpat_assum ‘peg_eval _ (_, nt (mkNT nTypeList2) _) _’ o
                   mp_then (Pos last) mp_tac) >>
      rpt kill_asm_guard >> strip_tac >> rveq >> simp[] >>
      imp_res_tac length_no_greater >> fs[] >>
      first_x_assum (qpat_assum ‘peg_eval _ (_, nt (mkNT nTyOp) _) _’ o
                     mp_then (Pos last) mp_tac) >> simp[] >>
      strip_tac >> rveq >> dsimp[])
  >- (print_tac "nDType" >> strip_tac >> rveq >> simp[] >>
      `NT_rank (mkNT nTbase) < NT_rank (mkNT nDType)`
        by simp[NT_rank_def] >>
      first_x_assum drule_all >>
      disch_then (qxchl [`base_pt`] strip_assume_tac) >> rveq >> simp[] >>
      drule_then strip_assume_tac
        (MATCH_MP not_peg0_LENGTH_decreases peg0_nTbase) >>
      qpat_x_assum `peg_eval cmlPEG (II, rpt XX FF) YY` mp_tac >>
      simp[peg_eval_rpt] >> disch_then (qxchl [`tyops`] strip_assume_tac) >>
      rveq >> simp[] >>
      asm_match `peg_eval_list cmlPEG (i1, nt (mkNT nTyOp) I) (i,tyops,err)`>>
      pop_assum mp_tac >>
      `∃i2. LENGTH i2 < LENGTH i0 ∧ i1 = i2` by simp[] >>
      pop_assum SUBST1_TAC >> pop_assum mp_tac >>
      `∃acc.
         ptree_head acc = NN nDType ∧ valid_lptree cmlG acc ∧
         real_fringe base_pt ++ MAP (TK ## I) i2 =
           real_fringe acc ++ MAP (TK ## I) i2 ∧
         mkNd (mkNT nDType) [base_pt] = acc`
        by (simp[cmlG_FDOM, cmlG_applied]) >>
      ntac 2 (pop_assum SUBST1_TAC) >> ntac 2 (pop_assum mp_tac) >>
      map_every qid_spec_tac [‘err’, `acc`, `i2`, `i`, `tyops`] >> Induct
      >- (simp[Once peg_eval_cases] >>
          simp[cmlG_FDOM, cmlG_applied, PULL_EXISTS]) >>
      qx_genl_tac [`tyop`, `i`, `i2`, `acc`, ‘err’] >>
      simp[Once peg_eval_cases] >> ntac 3 strip_tac >>
      disch_then (qxchl [‘eo0’, `i3`] strip_assume_tac) >>
      first_x_assum (erule mp_tac) >>
      disch_then (qxchl [`tyop_pt2`] strip_assume_tac) >> rveq >>
      simp[] >>
      `LENGTH i3 < LENGTH i2`
        by metis_tac[not_peg0_LENGTH_decreases, peg0_nTyOp] >>
      `LENGTH i3 < LENGTH i0` by decide_tac >>
      first_x_assum
        (qspecl_then [`i`, `i3`, `mkNd (mkNT nDType) [acc; tyop_pt2]`]
                     mp_tac)>>
      simp[cmlG_applied, cmlG_FDOM, DISJ_IMP_THM, FORALL_AND_THM] >>
      metis_tac[])
  >- (print_tac "nType" >> simp[peg_eval_choice] >>
      `NT_rank (mkNT nPType) < NT_rank (mkNT nType)` by simp[NT_rank_def] >>
      strip_tac >> rveq >> simp[]
      >- (first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
          fs[MAP_EQ_CONS, MAP_EQ_APPEND] >> rveq >>
          first_x_assum (qpat_assum ‘peg_eval _ (_, nt (mkNT nType) _) _’ o
                         mp_then (Pos last) mp_tac) >>
          simp[] >> strip_tac >> rveq >> dsimp[cmlG_FDOM, cmlG_applied] >>
          metis_tac[]) >>
      first_x_assum (erule strip_assume_tac) >> rveq >>
      dsimp[cmlG_applied, cmlG_FDOM])
  >- (print_tac "nPbaseList1" >> strip_tac >> rveq >>
      simp[cmlG_FDOM, cmlG_applied] >>
      `NT_rank (mkNT nPbase) < NT_rank (mkNT nPbaseList1)`
        by simp[NT_rank_def] >>
      first_x_assum (erule strip_assume_tac) >> rveq >>
      dsimp[MAP_EQ_CONS] >> csimp[] >>
      fs[MAP_EQ_APPEND] >> disj2_tac >>
      erule assume_tac (MATCH_MP not_peg0_LENGTH_decreases peg0_nPbase) >>
      first_x_assum (erule strip_assume_tac) >> simp[] >> metis_tac[])
  >- (print_tac "nFDecl" >> strip_tac >> rveq >> simp[] >>
      `NT_rank (mkNT nV) < NT_rank (mkNT nFDecl)` by simp[NT_rank_def] >>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      erule assume_tac
        (MATCH_MP not_peg0_LENGTH_decreases peg0_nV |> GEN_ALL) >>
      first_assum (erule strip_assume_tac) >> rveq >> dsimp[] >>
      first_assum (assume_tac o MATCH_MP length_no_greater o
                   assert (free_in ``nPbaseList1`` o concl)) >> fs[] >>
      first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nE``) o concl)) >>
      simp[] >> strip_tac >> rveq >> simp[cmlG_FDOM, cmlG_applied])
  >- (print_tac "nAndFDecls" >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      dsimp[SUBSET_DEF, pegsym_to_sym_def, DISJ_IMP_THM, FORALL_AND_THM,
            cmlG_applied, cmlG_FDOM, EXISTS_PROD, SF SFY_ss] >>
      first_x_assum match_mp_tac >>
      simp[NT_rank_def])
  >- (print_tac "nPE'" >> strip_tac >> rveq >> simp[] >>
      `NT_rank (mkNT nPattern) < NT_rank (mkNT nPE')` by simp[NT_rank_def] >>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      first_assum (assume_tac o MATCH_MP length_no_greater o
                   assert (free_in ``nPattern`` o concl)) >> fs[] >>
      first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nE'``) o concl)) >>
      simp[] >> strip_tac >> rveq >> dsimp[cmlG_FDOM, cmlG_applied])
  >- (print_tac "nPE" >> strip_tac >> rveq >> simp[] >>
      `NT_rank (mkNT nPattern) < NT_rank (mkNT nPE)` by simp[NT_rank_def] >>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      first_assum (assume_tac o MATCH_MP length_no_greater o
                   assert (free_in ``nPattern`` o concl)) >> fs[] >>
      first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nE``) o concl)) >>
      simp[] >> strip_tac >> rveq >> dsimp[cmlG_FDOM, cmlG_applied])
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
      simp[] >> strip_tac >> rveq >> dsimp[])
  >- (print_tac "nE'" >> simp[EXISTS_PROD] >> strip_tac >> rveq >> simp[] >>
      fs[]
      >- ((* raise case *)
          first_x_assum (first_assum o mp_then (Pos last) mp_tac) >>
          dsimp[cmlG_FDOM, cmlG_applied])
      >- ((* ElogicOR case *)
          loseC ``LENGTH`` >>
          first_x_assum (first_assum o mp_then (Pos last) mp_tac) >>
          dsimp[NT_rank_def,cmlG_FDOM, cmlG_applied])
      >- ((* if-then-else case *) loseC ``NT_rank`` >>
          first_assum (resolve_then Any drule (DECIDE “x < SUC x”)) >>
          strip_tac >> rveq >> simp[] >>
          first_assum (assume_tac o MATCH_MP length_no_greater o
                       assert (free_in ``ThenT`` o concl)) >> fs[] >>
          first_assum (qpat_assum ‘peg_eval _ _ (Success((ElseT,_)::_) _ _)’ o
                       mp_then (Pos last) mp_tac) >> impl_tac >- simp[] >>
          strip_tac >> rveq >> simp[] >>
          first_assum (assume_tac o MATCH_MP length_no_greater o
                       assert (free_in ``ElseT`` o concl)) >> fs[] >>
          first_x_assum (qpat_assum ‘peg_eval _ (_, nt (mkNT nE') I) _’ o
                         mp_then (Pos last) mp_tac) >> impl_tac >- simp[] >>
          strip_tac >> rveq >> dsimp[cmlG_applied, cmlG_FDOM])
      >- ((* bogus raise ElogicOR case *)
          loseC ``LENGTH`` >> first_x_assum (fn patth =>
          first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          simp[NT_rank_def] >> strip_tac >> rveq >>
          simp[cmlG_applied, cmlG_FDOM]))
  >- (print_tac "nE" >> simp[EXISTS_PROD] >> strip_tac >> rveq >> simp[] >> fs[]
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
          qpat_x_assum `peg_eval _ _ (Success((ThenT,_)::Y) Z _)`kall_tac >>
          qpat_x_assum `peg_eval _ _ (Success((ElseT,_)::Y) Z _)`kall_tac >>
          loseC ``NT_rank`` >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          simp[] >> metis_tac[])
      >- ((* fn x => e case *) loseC ``NT_rank`` >>
          first_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nPattern``) o concl)) >>
          rpt kill_asm_guard >> strip_tac >> rveq >>
          first_assum (assume_tac o MATCH_MP length_no_greater o
                       assert (free_in ``nPattern`` o concl)) >> fs[] >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nE``) o concl)) >>
          simp[] >> strip_tac >> rveq >> dsimp[cmlG_FDOM, cmlG_applied])
      >- ((* "case" E "of" PEs case *) loseC ``NT_rank`` >>
          first_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nE``) o concl)) >>
          rpt kill_asm_guard >> strip_tac >> rveq >> simp[] >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nPEs``) o concl)) >>
          first_assum (assume_tac o MATCH_MP length_no_greater o
                       assert (free_in ``nE`` o concl)) >> fs[] >>
          simp[] >> strip_tac >> rveq >> dsimp[cmlG_applied, cmlG_FDOM]) >>
      (* raise-ehandle case *)
      loseC ``LENGTH`` >> first_x_assum (fn patth =>
        first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
      simp[NT_rank_def] >> strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM])
  >- (print_tac "nEhandle" >> simp[EXISTS_PROD] >>
      `NT_rank (mkNT nElogicOR) < NT_rank (mkNT nEhandle)`
        by simp[NT_rank_def] >>
      strip_tac >> rveq >> simp[] >>
      first_x_assum (erule strip_assume_tac) >> rveq >>
      dsimp[cmlG_FDOM, cmlG_applied] >>
      first_assum (assume_tac o MATCH_MP length_no_greater o
                   assert (free_in ``nElogicOR`` o concl)) >> fs[] >>
      first_assum (fn patth =>
         first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                      assert (free_in ``nPEs``) o concl)) >>
      rpt kill_asm_guard >> strip_tac >> rveq >> simp[])
  >- (print_tac "nElogicOR" >> simp[EXISTS_PROD] >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[cmlG_applied, cmlG_FDOM, pegsym_to_sym_def, DISJ_IMP_THM,
           FORALL_AND_THM, SUBSET_DEF, EXISTS_PROD] >>
      dsimp[NT_rank_def, SF SFY_ss])
  >- (print_tac "nElogicAND" >> simp[EXISTS_PROD] >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[cmlG_applied, cmlG_FDOM, pegsym_to_sym_def, DISJ_IMP_THM,
           FORALL_AND_THM, SUBSET_DEF, EXISTS_PROD] >>
      dsimp[NT_rank_def, SF SFY_ss])
  >- (print_tac "nEtyped" >>
      `NT_rank (mkNT nEbefore) < NT_rank (mkNT nEtyped)`
        by simp[NT_rank_def] >> strip_tac >> rveq >>
      simp[cmlG_FDOM, cmlG_applied] >>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      first_x_assum (assume_tac o MATCH_MP length_no_greater o
                     assert (free_in ``nEbefore`` o concl)) >> fs[] >>
      first_x_assum (fn patth =>
         first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                      assert (free_in ``nType``) o concl)) >> simp[] >>
      strip_tac >> rveq >> dsimp[])
  >- (print_tac "nEbefore" >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[cmlG_applied, cmlG_FDOM, pegsym_to_sym_def, DISJ_IMP_THM,
           FORALL_AND_THM, SUBSET_DEF] >>
      dsimp[NT_rank_def, EXISTS_PROD, SF SFY_ss])
  >- (print_tac "nEcomp" >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[cmlG_applied, cmlG_FDOM, pegsym_to_sym_def, DISJ_IMP_THM,
           FORALL_AND_THM, SUBSET_DEF] >>
      dsimp[NT_rank_def, EXISTS_PROD, SF SFY_ss])
  >- (print_tac "nErel" >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[cmlG_applied, cmlG_FDOM, pegsym_to_sym_def, DISJ_IMP_THM,
           FORALL_AND_THM, SUBSET_DEF] >>
      dsimp[NT_rank_def, EXISTS_PROD, SF SFY_ss])
  >- (print_tac "nElistop" >>
      `NT_rank (mkNT nEadd) < NT_rank (mkNT nElistop)`
        by simp[NT_rank_def] >> strip_tac >> rveq >>
      simp[cmlG_FDOM, cmlG_applied] >>
      first_x_assum (erule strip_assume_tac) >> rveq >>
      simp[listTheory.APPEND_EQ_CONS] >>
      first_assum (mp_tac o
                   PART_MATCH (lhand o rand) not_peg0_LENGTH_decreases o
                   assert (free_in ``nEadd``) o concl) >>
      simp[] >> strip_tac >>
      first_assum (erule strip_assume_tac) >>
      rveq >> dsimp[MAP_EQ_CONS] >> csimp[] >>
      first_x_assum (assume_tac o MATCH_MP length_no_greater o
                     assert (free_in ``nListOps`` o concl)) >>
      metis_tac[DECIDE ``x ≤ y ∧ y < z ⇒ x < z:num``])
  >- (print_tac "nEadd" >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[cmlG_applied, cmlG_FDOM, pegsym_to_sym_def, DISJ_IMP_THM,
           FORALL_AND_THM, SUBSET_DEF] >>
      dsimp[NT_rank_def, EXISTS_PROD, SF SFY_ss])
  >- (print_tac "nEmult" >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[cmlG_applied, cmlG_FDOM, pegsym_to_sym_def, DISJ_IMP_THM,
           FORALL_AND_THM, SUBSET_DEF] >>
      simp[NT_rank_def, EXISTS_PROD, SF SFY_ss])
  >- (print_tac "nEseq" >>
      `NT_rank (mkNT nE) < NT_rank (mkNT nEseq)` by simp[NT_rank_def] >>
      strip_tac >> rveq >>
      dsimp[cmlG_FDOM, cmlG_applied, MAP_EQ_APPEND, MAP_EQ_CONS,
            listTheory.APPEND_EQ_CONS]
      >- (first_x_assum (erule mp_tac) >> strip_tac >> rveq >> csimp[] >>
          first_assum (mp_tac o MATCH_MP length_no_greater o
                       assert (free_in ``nE`` o concl)) >> simp[] >>
          strip_tac >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``nEseq``) o concl)) >>
          simp[] >> strip_tac >> rveq >> simp[] >>
          fs[MAP_EQ_APPEND, MAP_EQ_CONS] >> rveq >> fs[MAP_EQ_APPEND])
      >- (DISJ2_TAC >>
          first_x_assum (fn patth =>
           first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          simp[NT_rank_def] >> strip_tac >> rveq >> simp[] >>
          fs[MAP_EQ_APPEND] >> metis_tac[]) >>
      DISJ2_TAC >>
      first_x_assum (fn patth =>
        first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
      simp[NT_rank_def] >> strip_tac >> rveq >> simp[] >>
      fs[MAP_EQ_APPEND, MAP_EQ_CONS, PAIR_MAP] >> metis_tac[PAIR])
  >- (print_tac "nEbase" >>
      `NT_rank (mkNT nFQV) < NT_rank (mkNT nEbase) ∧
       NT_rank (mkNT nConstructorName) < NT_rank (mkNT nEbase)`
        by simp[NT_rank_def] >>
      CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ DNF_ss ++ CONJ_ss)
                                     [EXISTS_PROD])) >>
      strip_tac >> rveq >>
      simp[cmlG_FDOM, cmlG_applied] >>
      fs[peg_eval_nConstructor_wrongtok, peg_eval_nFQV_wrongtok] >>
      rpt (qpat_x_assum `peg_eval _ _ (Failure _ _)` (K ALL_TAC))
      >- (`NT_rank (mkNT nEliteral) < NT_rank (mkNT nEbase)`
            by simp[NT_rank_def] >>
          first_x_assum (pop_assum o mp_then Any mp_tac) >>
          disch_then (IMP_RES_THEN strip_assume_tac) >> rveq >> simp[])
      >- (* () *) dsimp[]
      >- ((* peg_EbaseParen 1 *)
          IMP_RES_THEN match_mp_tac peg_EbaseParen_sound >> simp[SF SFY_ss])
      >- ((* [ elist1 ] *)
          rpt (loseC ``NT_rank``) >>
          first_x_assum $ drule_at (Pos last) >>
          rpt kill_asm_guard >> strip_tac >> rveq >> dsimp[])
      >- ((* [ ] *) dsimp[])
      >- ((* "let" ... "in" ... "end" case *)
          rpt (loseC ``NT_rank``) >>
          first_assum (resolve_then Any drule (DECIDE “x < SUC x”)) >>
          rpt kill_asm_guard >> strip_tac >> rveq >> dsimp[] >>
          first_x_assum (assume_tac o MATCH_MP length_no_greater o
                         assert (free_in ``nLetDecs`` o concl)) >> fs[] >>
          first_x_assum $ drule_at Any >> simp[] >> strip_tac >> rveq >>
          dsimp[])
      >- ((* FQV *) first_x_assum (erule strip_assume_tac) >> rveq >> simp[])
      >- ((* nCons *)first_x_assum (erule strip_assume_tac) >> rveq >> simp[])
      >- ((* nOpID *)
          rpt (loseC ``NT_rank``) >> first_x_assum $ drule_at Any >>
          simp[] >> strip_tac >> rveq >> dsimp[]) >>
      IMP_RES_THEN mp_tac peg_EbaseParen_sound >> simp[SF SFY_ss])
  >- (print_tac "nEliteral" >> strip_tac >> rveq >>
      simp[cmlG_applied, cmlG_FDOM] >> rename [`tk = StringT _`] >>
      Cases_on `tk` >> fs[])
  >- (print_tac "nOpID" >> strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM] >>
      fs[] >> rveq >> fs[PAIR_MAP])
  >- (print_tac "nCompOps">> strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM])
  >- (print_tac "nListOps">> dsimp[EXISTS_PROD, cmlG_applied, cmlG_FDOM])
  >- (print_tac "nRelOps" >> dsimp[EXISTS_PROD, cmlG_applied, cmlG_FDOM])
  >- (print_tac "nAddOps" >> dsimp[EXISTS_PROD, cmlG_applied, cmlG_FDOM])
  >- (print_tac "nMultOps">> dsimp[EXISTS_PROD, cmlG_applied, cmlG_FDOM])
  >- (print_tac "nElist1" >>
      `NT_rank (mkNT nE) < NT_rank (mkNT nElist1)`
        by simp[NT_rank_def] >> strip_tac >> rveq
      >- (first_x_assum (erule mp_tac) >> strip_tac >> rveq >>
          simp[cmlG_FDOM, cmlG_applied, PULL_EXISTS, SF CONJ_ss, DISJ_IMP_THM,
               GSYM CONJ_ASSOC] >> first_x_assum irule >>
          IMP_RES_TAC length_no_greater >> fs[] >> simp[SF SFY_ss])
      >- (first_x_assum (erule mp_tac) >> dsimp[cmlG_applied, cmlG_FDOM]) >>
      first_x_assum (erule mp_tac) >> dsimp[cmlG_FDOM, cmlG_applied])
  >- (print_tac "nEapp" >> simp[peg_eval_choice] >>
      strip_tac >> rpt (qpat_x_assum `peg_eval _ _ (Failure _ _)` kall_tac) >>
      rveq >> simp[] >>
      `NT_rank (mkNT nEbase) < NT_rank (mkNT nEapp)` by simp[NT_rank_def]>>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      erule assume_tac
        (MATCH_MP not_peg0_LENGTH_decreases peg0_nEbase |> GEN_ALL) >>
      rename [‘peg_eval _ (i0, nt (mkNT nEbase) I) (Success i1 [pt] _)’,
              ‘peg_eval _ (i1,rpt(nt(mkNT nEbase) I) FLAT) (Success i r _)’] >>
      qpat_x_assum ‘peg_eval G (i1, rpt X R) Y’ mp_tac >>
      simp[peg_eval_rpt] >> disch_then (qxchl [`pts`] strip_assume_tac) >>
      rveq >>
      `∃acc. real_fringe pt = FLAT (MAP real_fringe acc) ∧
             [pt] = acc ∧ MAP ptree_head acc ∈ cmlG.rules ' (mkNT nEapp) ∧
             (∀pt. MEM pt acc ⇒ valid_lptree cmlG pt)`
        by simp[cmlG_applied, cmlG_FDOM] >>
      ntac 2 (pop_assum mp_tac) >> ntac 2 (pop_assum SUBST1_TAC) >>
      Q.UNDISCH_THEN `LENGTH i1 < LENGTH i0` mp_tac >>
      qpat_x_assum `peg_eval_list X Y Z` mp_tac >>
      map_every qid_spec_tac [‘err’,‘i’, ‘i1’, ‘acc’, ‘pts’] >> Induct
      >- simp[Once peg_eval_cases, cmlG_FDOM, PULL_EXISTS] >>
      simp[Once peg_eval_cases] >>
      qx_genl_tac [‘pt'’, ‘acc’, ‘i2’, ‘i’, ‘err’] >>
      disch_then (qxchl [‘eo0’, `i3`] strip_assume_tac) >>
      ntac 3 strip_tac >>
      first_x_assum (qpat_assum ‘peg_eval _ (i2, nt(mkNT nEbase) I) _’ o
                     mp_then (Pos last) mp_tac) >>
      rpt kill_asm_guard >> disch_then (qxchl [`ebpt`] strip_assume_tac) >>
      rveq >> simp[] >>
      first_x_assum (assume_tac o MATCH_MP length_no_greater o
                     assert (free_in ``ebpt:mlptree`` o concl)) >>
      simp[] >>
      first_x_assum
        (qspecl_then [`[mkNd (mkNT nEapp) acc; ebpt]`, `i3`, `i`, ‘err’]
                     mp_tac) >>
      rpt kill_asm_guard >> dsimp[cmlG_FDOM, cmlG_applied])
  >- (print_tac "nFQV" >>
      simp[peg_longV_def, pairTheory.EXISTS_PROD] >>
      strip_tac >> rveq >> dsimp[cmlG_FDOM, cmlG_applied]
      >- (`NT_rank (mkNT nV) < NT_rank (mkNT nFQV)` by simp[NT_rank_def] >>
          first_x_assum (erule strip_assume_tac) >> rveq >> simp[]) >>
      asm_match `destLongidT litok = SOME(mp,vp)` >> Cases_on `litok` >> fs[])
  >- (print_tac "nTyvarN" >> dsimp[EXISTS_PROD] >> rw[] >>
      simp[cmlG_FDOM, cmlG_applied] >>
      asm_match `isTyvarT h` >> Cases_on `h` >> fs[]) >>
  print_tac "nV" >>
  simp[peg_V_def, peg_eval_choice] >>
  strip_tac >> rveq >> dsimp[cmlG_FDOM, cmlG_applied, PAIR_MAP]
QED

val _ = export_theory()
