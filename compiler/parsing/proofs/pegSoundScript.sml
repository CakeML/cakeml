(*
  Soundness proof for the parser. If the parser returns a parse tree,
  then it is valid w.r.t. the specification grammar.
*)
open preamble pegTheory cmlPEGTheory gramTheory gramPropsTheory
     grammarTheory

val _ = new_theory "pegSound";
val _ = set_grammar_ancestry ["cmlPEG", "gramProps"]

val d = let
  val d0 = TypeBase.distinct_of ``:(α,β,γ)pegsym``
in
  CONJ d0 (GSYM d0)
end
val i = TypeBase.one_one_of ``:(α,β,γ)pegsym``

infix >*
fun t1 >* t2 = (t1 >> conj_tac) >- t2

Theorem peg_eval_choicel_NIL[simp]:
   peg_eval G (i0, choicel []) x = (x = NONE)
Proof
  simp[choicel_def, Once peg_eval_cases]
QED

Theorem peg_eval_choicel_CONS:
   ∀x. peg_eval G (i0, choicel (h::t)) x ⇔
          peg_eval G (i0, h) x ∧ x <> NONE ∨
          peg_eval G (i0,h) NONE ∧ peg_eval G (i0, choicel t) x
Proof
  simp[choicel_def, SimpLHS, Once peg_eval_cases] >>
  simp[sumID_def, pairTheory.FORALL_PROD, optionTheory.FORALL_OPTION]
QED

Theorem peg_eval_seql_NIL[simp]:
   peg_eval G (i0, seql [] f) x ⇔ (x = SOME(i0,f []))
Proof
  simp[seql_def, pegf_def] >> simp[Once peg_eval_cases]
QED

Theorem peg_eval_try:
   ∀x. peg_eval G (i0, try s) x ⇔
         peg_eval G (i0, s) NONE ∧ x = SOME(i0,[]) ∨
         ∃i r. peg_eval G (i0, s) (SOME(i,r)) ∧ x = SOME(i,r)
Proof
  simp[Once peg_eval_cases, try_def, SimpLHS, choicel_def,
       peg_eval_choice] >> simp[sumID_def] >> metis_tac[]
QED

Theorem peg_eval_seql_CONS:
   ∀x. peg_eval G (i0, seql (h::t) f) x ⇔
          peg_eval G (i0, h) NONE ∧ x = NONE ∨
          (∃rh i1. peg_eval G (i0,h) (SOME(i1,rh)) ∧
                   peg_eval G (i1, seql t I) NONE ∧ x = NONE) ∨
          (∃rh i1 i rt. peg_eval G (i0, h) (SOME(i1,rh)) ∧
                        peg_eval G (i1, seql t I) (SOME(i,rt)) ∧
                        x = SOME(i,f(rh ++ rt)))
Proof
  simp[seql_def, pegf_def] >>
  simp[SimpLHS, Once peg_eval_cases] >>
  simp[optionTheory.FORALL_OPTION, pairTheory.FORALL_PROD] >>
  conj_tac
  >- (simp[peg_eval_seq_NONE] >> metis_tac[]) >>
  simp[peg_eval_seq_SOME] >> dsimp[] >> metis_tac[]
QED

val peg_eval_choicel_SING = save_thm(
  "peg_eval_choicel_SING",
  CONJ
    (``peg_eval G (i0, choicel [sym]) (SOME x)``
       |> SIMP_CONV (srw_ss()) [peg_eval_choicel_CONS, peg_eval_choicel_NIL])
    (``peg_eval G (i0, choicel [sym]) NONE``
       |> SIMP_CONV (srw_ss()) [peg_eval_choicel_CONS, peg_eval_choicel_NIL]));

Theorem not_peg0_LENGTH_decreases:
   ¬peg0 G s ⇒ peg_eval G (i0, s) (SOME(i,r)) ⇒ LENGTH i < LENGTH i0
Proof
  metis_tac[peg_eval_suffix', lemma4_1a]
QED


val _ = augment_srw_ss [rewrites [
  peg_eval_seql_CONS, peg_eval_tok_SOME, tokeq_def, bindNT_def, mktokLf_def,
  peg_eval_choicel_CONS, pegf_def, peg_eval_seq_SOME, pnt_def, peg_eval_try,
  try_def]]

Theorem peg_eval_TypeDec_wrongtok:
   FST tk ≠ DatatypeT ⇒ ¬peg_eval cmlPEG (tk::i, nt (mkNT nTypeDec) f) (SOME x)
Proof
  simp[Once peg_eval_cases, cmlpeg_rules_applied, FDOM_cmlPEG,
       peg_TypeDec_def, peg_eval_seq_SOME, tokeq_def, peg_eval_tok_SOME]
QED

Theorem peg_eval_TypeAbbrevDec_wrongtok:
   FST tk ≠ TypeT ⇒ ¬peg_eval cmlPEG (tk::i, nt (mkNT nTypeAbbrevDec) f) (SOME x)
Proof
  simp[Once peg_eval_cases, cmlpeg_rules_applied, FDOM_cmlPEG,
       peg_eval_seq_SOME, tokeq_def, peg_eval_tok_SOME]
QED

Theorem peg_eval_LetDec_wrongtok:
   FST tk = SemicolonT ⇒ ¬peg_eval cmlPEG (tk::i, nt (mkNT nLetDec) f) (SOME x)
Proof
  simp[Once peg_eval_cases, cmlpeg_rules_applied, FDOM_cmlPEG,
       peg_TypeDec_def, peg_eval_seq_SOME, tokeq_def, peg_eval_tok_SOME,
       peg_eval_choicel_CONS, peg_eval_seql_CONS]
QED

Theorem peg_eval_nUQConstructor_wrongtok:
   (∀s. FST t ≠ AlphaT s) ⇒
    ¬peg_eval cmlPEG (t::i, nt (mkNT nUQConstructorName) f) (SOME x)
Proof
  simp[Once peg_eval_cases, cmlpeg_rules_applied,
       peg_eval_tok_SOME,
       peg_UQConstructorName_def] >> Cases_on `t` >> simp[]
QED

Theorem peg_eval_nConstructor_wrongtok:
   (∀s. FST t ≠ AlphaT s) ∧ (∀s1 s2. FST t ≠ LongidT s1 s2) ⇒
    ¬peg_eval cmlPEG (t::i, nt (mkNT nConstructorName) f) (SOME x)
Proof
  simp[Once peg_eval_cases, cmlpeg_rules_applied, peg_eval_tok_SOME,
       peg_eval_choicel_CONS, peg_eval_seq_NONE, pegf_def, pnt_def,
       peg_eval_nUQConstructor_wrongtok, peg_eval_seq_SOME] >>
  Cases_on `t` >> simp[]
QED

Theorem peg_eval_nV_wrongtok:
   (∀s. FST t ≠ AlphaT s) ∧ (∀s. FST t ≠ SymbolT s) ⇒
    ¬peg_eval cmlPEG (t::i, nt (mkNT nV) f) (SOME x)
Proof
  simp[Once peg_eval_cases, cmlpeg_rules_applied, peg_V_def,
       peg_eval_seq_NONE, peg_eval_choice] >>
  Cases_on `t` >> simp[]
QED

Theorem peg_eval_nFQV_wrongtok:
   (∀s. FST t ≠ AlphaT s) ∧ (∀s. FST t ≠ SymbolT s) ∧ (∀s1 s2. FST t ≠ LongidT s1 s2) ⇒
    ¬peg_eval cmlPEG (t::i, nt (mkNT nFQV) f) (SOME x)
Proof
  simp[Once peg_eval_cases, cmlpeg_rules_applied,
       peg_eval_seq_NONE, peg_eval_choice, peg_eval_nV_wrongtok] >>
  Cases_on `t` >> simp[peg_longV_def]
QED

Theorem peg_eval_rpt_never_NONE:
   ¬peg_eval G (i, rpt sym f) NONE
Proof
  simp[Once peg_eval_cases]
QED
val _ = export_rewrites ["peg_eval_rpt_never_NONE"]

val pegsym_to_sym_def = Define`
  (pegsym_to_sym (tok P f) = if f = mktokLf then { TK t | P t } else ∅) ∧
  pegsym_to_sym (nt N f) = { NT N } ∧
  pegsym_to_sym _ = {}
`

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
   ∀UpperN sym sepsym i0 i pts.
      peg_eval cmlPEG (i0, peg_linfix UpperN sym sepsym) (SOME(i,pts)) ⇒
      (∀i0' i pts s.
         s ∈ {sym;sepsym} ⇒
         LENGTH i0' < LENGTH i0 ⇒
         peg_eval cmlPEG (i0',s) (SOME(i,pts)) ⇒
         ∃pt. pts = [pt] ∧ ptree_head pt ∈ pegsym_to_sym s ∧
              valid_lptree cmlG pt ∧
              MAP (TK ## I) i0' = real_fringe pt ++ MAP (TK ## I) i) ∧
      (∀i pts s.
         s ∈ {sym; sepsym} ⇒
         peg_eval cmlPEG (i0, s) (SOME(i,pts)) ⇒
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
  rpt strip_tac >> rveq >>
  asm_match `peg_eval cmlPEG (i0, sym) (SOME(i1,r1))` >>
  first_assum (qspecl_then [`i1`, `r1`, `sym`] mp_tac) >> simp_tac(srw_ss())[]>>
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
  map_every qid_spec_tac [`acc`, `i2`,`i`, `l`] >>
  Induct >- simp[Once peg_eval_cases, mk_linfix_def] >>
  simp[Once peg_eval_cases] >>
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
    by metis_tac[peg_eval_suffix',
                 DECIDE``x:num ≤ y ⇔ x = y ∨ x < y``] >>
  `LENGTH i2' < LENGTH i0` by decide_tac >>
  first_x_assum (qspecl_then [`i2'`, `i3'`, `sym_r`, `sym`] mp_tac) >>
  rpt kill_asm_guard >>
  disch_then (qxchl [`sym_pt`] strip_assume_tac) >> rveq >>
  simp[mk_linfix_def] >>
  `LENGTH i3' < LENGTH i2'` by metis_tac[not_peg0_LENGTH_decreases] >>
  `LENGTH i3' ≤ LENGTH i1` by decide_tac >>
  first_x_assum (qspecl_then [`i`, `i3'`, `[mkNd UpperN acc; sep_pt; sym_pt]`]
                             mp_tac) >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  `[NT UpperN; ptree_head sep_pt; ptree_head sym_pt] ∈ cmlG.rules ' UpperN`
    by fs[SUBSET_DEF] >>
  simp[]
QED

Theorem length_no_greater:
   peg_eval G (i0, sym) (SOME(i,r)) ⇒ LENGTH i ≤ LENGTH i0
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
   FST tk = LparT ⇒ ¬peg_eval cmlPEG (tk::i, nt (mkNT nTyOp) f) (SOME x)
Proof
  simp[Once peg_eval_cases, cmlpeg_rules_applied, FDOM_cmlPEG] >>
  simp[Once peg_eval_cases, cmlpeg_rules_applied, FDOM_cmlPEG]
QED

datatype disposition = X | KEEP
fun rlresolve d P k = let
  val f = case d of X => first_x_assum | _ => first_assum
in
  f (fn patth =>
      first_assum (k o PART_MATCH (rand o lhand) patth o
                   assert P o concl))
end
fun lrresolve d P k = let
  val f = case d of X => first_x_assum | _ => first_assum
in
  f (fn patth =>
      first_assum (k o PART_MATCH (lhand o rand) patth o
                   assert P o concl))
end

Theorem peg_EbaseParen_sound:
   ∀i0 i pts.
      peg_eval cmlPEG (i0, peg_EbaseParen) (SOME(i,pts)) ⇒
      (∀i0' N i pts.
        LENGTH i0' < LENGTH i0 ∧
        peg_eval cmlPEG (i0', nt (mkNT N) I) (SOME(i,pts)) ⇒
        ∃pt.
           pts = [pt] ∧ ptree_head pt = NT (mkNT N) ∧
           valid_lptree cmlG pt ∧
           MAP (TOK ## I) i0' = real_fringe pt ++ MAP (TOK ## I) i) ⇒
      ∃pt.
        pts = [pt] ∧ ptree_head pt = NT (mkNT nEbase) ∧
        valid_lptree cmlG pt ∧
        MAP (TOK ## I) i0 = real_fringe pt ++ MAP (TOK ## I) i
Proof
  rw[peg_EbaseParen_def]
  >- (rlresolve X (K true) mp_tac >> simp[] >> strip_tac >> rveq >>
      simp[peg_EbaseParenFn_def, cmlG_FDOM, cmlG_applied, DISJ_IMP_THM,
           pairTheory.PAIR_MAP])
  >- (rlresolve KEEP (free_in ``nE``) mp_tac >>
      rpt kill_asm_guard >> strip_tac >> rveq >>
      rlresolve X (free_in ``nElist1``) mp_tac >>
      first_assum (mp_tac o MATCH_MP length_no_greater o
                   assert (free_in ``nE`` o concl)) >>
      simp[] >> rw[] >>
      rpt (qpat_x_assum`_ = FST _`(assume_tac o SYM)) >> rw[] >>
      simp[peg_EbaseParenFn_def, cmlG_applied, cmlG_FDOM,
           DISJ_IMP_THM, FORALL_AND_THM, pairTheory.PAIR_MAP]) >>
  rlresolve KEEP (free_in ``nE``) mp_tac >> rpt kill_asm_guard >>
  strip_tac >> rveq >>
  rlresolve X (free_in ``nEseq``) mp_tac >>
  first_assum (mp_tac o MATCH_MP length_no_greater o
               assert (free_in ``nE`` o concl)) >>
  simp[] >> rpt strip_tac >>rveq >>
  rpt (qpat_x_assum`_ = FST _`(assume_tac o SYM)) >>
  simp[peg_EbaseParenFn_def, cmlG_applied, cmlG_FDOM,
       DISJ_IMP_THM, FORALL_AND_THM, pairTheory.PAIR_MAP] >> fs[]
QED

val PAIR_MAP_I = Q.prove(
  ‘(f ## I) x = (f (FST x), SND x) ⇔ T’,
  simp[PAIR_MAP]);
val _ = augment_srw_ss [rewrites [PAIR_MAP_I]]


val bindNT0_lemma = REWRITE_RULE [GSYM mkNd_def] bindNT0_def
val _ = augment_srw_ss [rewrites [bindNT0_lemma]]

(* left recursive rules in the grammar turn into calls to rpt in the PEG,
   and this in turn requires inductions *)
Theorem ptPapply_lemma:
   ∀limit.
     (∀i0 i pts.
       LENGTH i0 < limit ⇒
       peg_eval cmlPEG (i0, nt (mkNT nPbase) I) (SOME (i, pts)) ⇒
       ∃pt. pts = [pt] ∧ ptree_head pt = NN nPbase ∧ valid_lptree cmlG pt ∧
            MAP (TK ## I) i0 = real_fringe pt ++ MAP (TK ## I) i) ⇒
     ∀ptlist pt0 acc i0.
       peg_eval_list cmlPEG (i0, nt (mkNT nPbase) I) (i, ptlist) ∧
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
  first_x_assum (erule mp_tac) >> strip_tac >> rveq >> simp[ptPapply0_def] >>
  imp_res_tac (MATCH_MP not_peg0_LENGTH_decreases peg0_nPbase) >>
  rename [‘peg_eval _ (i0, _) (SOME (i1, [pt1]))’,
          ‘peg_eval_list _ (i1, _) (i, ptlist)’] >>
  first_x_assum (qspecl_then [‘pt1’, ‘mkNd (mkNT nPConApp) [acc; pt0]’, ‘i1’]
                             mp_tac) >> simp[] >>
  disch_then irule >> dsimp[cmlG_applied, cmlG_FDOM]
QED

Theorem peg_sound:
   ∀N i0 i pts.
       peg_eval cmlPEG (i0,nt N I) (SOME(i,pts)) ⇒
       ∃pt. pts = [pt] ∧ ptree_head pt = NT N ∧
            valid_lptree cmlG pt ∧
            MAP (TOK ## I) i0 = real_fringe pt ++ MAP (TOK ## I) i
Proof
  ntac 2 gen_tac >> `?iN. iN = (i0,N)` by simp[] >> pop_assum mp_tac >>
  map_every qid_spec_tac [`i0`, `N`, `iN`] >>
  qispl_then [`measure (LENGTH:(token # locs) list->num) LEX measure NT_rank`]
             (ho_match_mp_tac o
              SIMP_RULE (srw_ss()) [pairTheory.WF_LEX,
                                    prim_recTheory.WF_measure])
             relationTheory.WF_INDUCTION_THM >>
  dsimp[pairTheory.LEX_DEF] >>
  map_every qx_gen_tac [`N`, `i0`, `i`, `pts`] >> strip_tac >>
  simp[peg_eval_NT_SOME, cmlPEGTheory.FDOM_cmlPEG] >>
  disch_then (CONJUNCTS_THEN2 strip_assume_tac mp_tac) >> rveq >>
  simp[cmlPEGTheory.cmlpeg_rules_applied, ptree_list_loc_def]
  >- (print_tac "nNonETopLevelDecs" >>
      `NT_rank (mkNT nTopLevelDec) < NT_rank (mkNT nNonETopLevelDecs)`
        by simp[NT_rank_def] >>
      strip_tac >> rveq >> dsimp[cmlG_FDOM, cmlG_applied]
      >- (first_x_assum (erule strip_assume_tac) >> rveq >> csimp[] >>
          rename1
           `peg_eval _ (inp0, nt (mkNT nTopLevelDec) _) (SOME (inp1,_))` >>
          `LENGTH inp1 < LENGTH inp0`
            by metis_tac[not_peg0_LENGTH_decreases, peg0_nTopLevelDec] >>
          csimp[PULL_EXISTS] >> metis_tac[])
      >- (fs[] >> csimp[] >> metis_tac[DECIDE ``x < SUC x``])
      >- (csimp[] >> fs[] >> metis_tac[DECIDE ``x < SUC x``]))
  >- (print_tac "nTopLevelDecs" >>
      `NT_rank (mkNT nE) < NT_rank (mkNT nTopLevelDecs) ∧
       NT_rank (mkNT nTopLevelDec) < NT_rank (mkNT nTopLevelDecs)`
          by simp[NT_rank_def] >>
      strip_tac >> rveq >> simp[cmlG_FDOM, cmlG_applied]
      >- (dsimp[APPEND_EQ_CONS] >> csimp[] >>
          first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
          rename1 `peg_eval _ (inp0, _) (SOME(h::inp1,[_]))` >>
          `LENGTH (h :: inp1) < LENGTH inp0`
            by metis_tac[not_peg0_LENGTH_decreases, peg0_nE] >>
          fs[] >> metis_tac[DECIDE ``SUC x < y ⇒ x < y``])
      >- (first_x_assum (erule strip_assume_tac) >> rveq >> dsimp[] >>
          csimp[] >>
          rename1
            `peg_eval _ (inp0, nt (mkNT nTopLevelDec) I) (SOME(inp1,_))` >>
          `LENGTH inp1 < LENGTH inp0` suffices_by metis_tac[] >>
          metis_tac[not_peg0_LENGTH_decreases, peg0_nTopLevelDec])
      >- (dsimp[] >> csimp[] >> fs[] >> metis_tac[DECIDE ``x < SUC x``])
      >- (dsimp[] >> csimp[] >> fs[] >> metis_tac[DECIDE ``x < SUC x``])
      >- (rename1 `peg_eval _ (ip0,nt (mkNT nTopLevelDec) _) (SOME(ip1,pt))`>>
          first_x_assum(qspecl_then [`mkNT nTopLevelDec`, `ip1`, `pt`] mp_tac)>>
          simp[] >> strip_tac >> rveq >> dsimp[] >> csimp[] >>
          `LENGTH ip1 < LENGTH ip0` suffices_by metis_tac[] >>
          metis_tac[not_peg0_LENGTH_decreases, peg0_nTopLevelDec])
      >- (dsimp[] >> csimp[] >> fs[] >> metis_tac[DECIDE ``x < SUC x``])
      >- (dsimp[] >> csimp[] >> fs[] >> metis_tac[DECIDE ``x < SUC x``])
      >- (rename1 `peg_eval _ (ip0,nt (mkNT nTopLevelDec) _) (SOME(ip1,pt))`>>
          first_x_assum(qspecl_then [`mkNT nTopLevelDec`, `ip1`, `pt`] mp_tac)>>
          simp[] >> strip_tac >> rveq >> dsimp[] >> csimp[] >>
          `LENGTH ip1 < LENGTH ip0` suffices_by metis_tac[] >>
          metis_tac[not_peg0_LENGTH_decreases, peg0_nTopLevelDec])
      >- (dsimp[] >> csimp[] >> fs[] >> metis_tac[DECIDE ``x < SUC x``])
      >- (dsimp[] >> csimp[] >> fs[] >> metis_tac[DECIDE ``x < SUC x``]))
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
      asm_match `peg_eval cmlPEG (vi, nt (mkNT nStructName) I) (SOME(opti,vt))` >>
      `LENGTH vi < SUC (LENGTH vi)` by decide_tac >>
      first_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      `LENGTH opti < LENGTH vi`
        by metis_tac[not_peg0_LENGTH_decreases, peg0_nStructName] >>
      `LENGTH opti < SUC (LENGTH vi)` by decide_tac >>
      first_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      asm_match `peg_eval cmlPEG (opti, OPTSIG)
                          (SOME (eqT::strT::di,[opt]))` >>
      `LENGTH (eqT::strT::di) ≤ LENGTH opti`
        by metis_tac[peg_eval_suffix',
                     DECIDE``x:num ≤ y ⇔ x < y ∨ x = y``] >> fs[] >>
      `LENGTH di < SUC (LENGTH vi)` by decide_tac >>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[])
  >- (print_tac "nStructName" >> simp[peg_StructName_def] >>
      dsimp[cmlG_applied, cmlG_FDOM, PAIR_MAP])
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
            `peg_eval cmlPEG (i0, nt (mkNT nSpecLine) I) (SOME (i1,r))` >>
          `LENGTH i1 < LENGTH i0`
            by metis_tac[not_peg0_LENGTH_decreases, peg0_nSpecLine] >>
          first_x_assum (erule mp_tac) >> rpt strip_tac >> rveq >> fs[])
      >- (dsimp[MAP_EQ_SING] >> csimp[]>>fs[] >> metis_tac[DECIDE``x < SUC x``])
      >> fs[cmlG_FDOM, cmlG_applied, MAP_EQ_SING] >> dsimp[] >> csimp[] >>
          metis_tac[DECIDE``x< SUC x``])
  >- (print_tac "nSpecLine" >> strip_tac >> rveq >>
      fs[cmlG_applied, cmlG_FDOM, peg_eval_TypeDec_wrongtok]
      >- (asm_match
            `peg_eval cmlPEG (i1, nt (mkNT nV) I) (SOME(colonT::i2,r))` >>
          `LENGTH i1 < SUC (LENGTH i1)` by DECIDE_TAC >>
          first_assum (erule strip_assume_tac) >>
          `LENGTH (colonT::i2) < LENGTH i1`
            by metis_tac[not_peg0_LENGTH_decreases, peg0_nV] >> fs[] >>
          `LENGTH i2 < SUC(LENGTH i1)` by decide_tac >>
          first_x_assum (erule strip_assume_tac) >> rveq >> dsimp[])
      >- (asm_match
            `peg_eval cmlPEG (i1, nt (mkNT nTypeName) I) (SOME(i2, nmpts))` >>
          first_assum (qspecl_then [`mkNT nTypeName`, `i1`, `i2`, `nmpts`]
                                   mp_tac) >>
          simp_tac (srw_ss()) [] >> ASM_REWRITE_TAC [] >>
          disch_then (qx_choose_then `nmpt` strip_assume_tac) >>
          dsimp[MAP_EQ_SING] >> csimp[] >>
          `LENGTH i2 < LENGTH i1`
            by metis_tac[not_peg0_LENGTH_decreases, peg0_nTypeName] >>
          `LENGTH i2 < SUC (LENGTH i1)` by simp[] >>
          metis_tac[])
      >- (dsimp[MAP_EQ_SING] >> csimp[] >> metis_tac[DECIDE``x<SUC x``])>>
      rpt(qpat_x_assum`_ = FST _`(assume_tac o SYM)) \\ fs[] >> rveq \\ fs[] >>
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
      >- (first_x_assum (erule strip_assume_tac) >>
          asm_match `peg_eval cmlPEG (i0,nt (mkNT nDecl) I) (SOME(i1,r))` >>
          dsimp[MAP_EQ_SING] >>
          `LENGTH i1 < LENGTH i0`
            by metis_tac[not_peg0_LENGTH_decreases,peg0_nDecl] >>
          first_x_assum (erule strip_assume_tac) >>
          dsimp[MAP_EQ_SING])
      >- (dsimp[MAP_EQ_SING] >> csimp[] >> metis_tac[DECIDE``x<SUC x``]) >>
      dsimp[MAP_EQ_SING] >> csimp[] >> metis_tac[DECIDE``x<SUC x``])
  >- (print_tac "nTypeAbbrevDec" >>
      rpt strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM] >>
      dsimp[listTheory.APPEND_EQ_CONS, MAP_EQ_SING] >> csimp[] >>
      qmatch_assum_rename_tac
        `peg_eval cmlPEG (inp, nt(mkNT nTypeName) I) (SOME(equalsT::inp1,t1))`>>
      first_assum
        (qspecl_then [`mkNT nTypeName`, `inp`, `equalsT::inp1`, `t1`] mp_tac) >>
      simp_tac (srw_ss()) [] >> ASM_REWRITE_TAC[] >>
      disch_then (qx_choose_then `tree1` strip_assume_tac) >> simp[] >>
      qmatch_assum_rename_tac
        `peg_eval cmlPEG (inp1, nt(mkNT nType) I) (SOME(inp2,t2))` >>
      `LENGTH (equalsT::inp1) < LENGTH inp`
        by metis_tac[not_peg0_LENGTH_decreases, peg0_nTypeName] >> fs[] >>
      `LENGTH inp1 < SUC (LENGTH inp)` by simp[] >>
      first_x_assum (qspecl_then [`mkNT nType`, `inp1`, `inp2`, `t2`] mp_tac) >>
      simp[] >> metis_tac[])
  >- (print_tac "nDecl" >>
      rpt strip_tac >> rveq >>
      rpt(qpat_x_assum`_ = FST _`(assume_tac o SYM)) >>
      fs[peg_eval_TypeDec_wrongtok, peg_eval_TypeAbbrevDec_wrongtok] >>
      rveq >> fs[]
      >- (asm_match `peg_eval cmlPEG (i1, nt (mkNT nPattern) I)
                              (SOME(equalsT::i2,r))` >>
          `LENGTH i1 < SUC (LENGTH i1)` by decide_tac >>
          first_assum (erule strip_assume_tac) >> rveq >>
          `LENGTH (equalsT::i2) ≤ LENGTH i1`
            by metis_tac[peg_eval_suffix',
                         DECIDE``x≤y ⇔ x = y ∨ x < y:num``] >> fs[]>>
          `LENGTH i2 < SUC (LENGTH i1)` by decide_tac >>
          first_x_assum (erule strip_assume_tac) >> rveq >>
          simp[cmlG_FDOM, cmlG_applied, MAP_EQ_SING] >> dsimp[PAIR_MAP])
      >- (dsimp[cmlG_applied, cmlG_FDOM, MAP_EQ_SING] >> csimp[PAIR_MAP] >>
          metis_tac[DECIDE ``x<SUC x``])
      >- (dsimp[cmlG_FDOM, cmlG_applied, MAP_EQ_SING] >> csimp[PAIR_MAP] >>
          metis_tac[DECIDE``x<SUC x``])
      >- (dsimp[cmlG_FDOM, cmlG_applied, APPEND_EQ_CONS] >> csimp[PAIR_MAP] >>
          rename[‘MAP (TK ## I) in0’, ‘peg_eval _ (in0, nt (mkNT nDecls) I)’] >>
          ‘LENGTH in0 < SUC (LENGTH in0)’ by simp[] >>
          first_assum (pop_assum o mp_then (Pos hd) drule) >>
          disch_then (qx_choose_then ‘decls1_pt’ strip_assume_tac) >> simp[] >>
          fs[MAP_EQ_APPEND] >> rveq >> dsimp[PAIR_MAP] >>
          rename [‘real_fringe decls1_pt = MAP _ in00’,
                  ‘peg_eval _ (in00 ++ [Int] ++ in01, nt (mkNT nDecls) I)’] >>
          first_x_assum (qpat_assum ‘peg_eval _ (in01, _) _’ o
                         mp_then (Pos (el 2)) mp_tac) >> dsimp[])
      >- (`NT_rank (mkNT nTypeDec) < NT_rank (mkNT nDecl)`
            by simp[NT_rank_def] >>
          first_x_assum (erule strip_assume_tac) >>
          dsimp[cmlG_FDOM, cmlG_applied])
      >- (`NT_rank (mkNT nTypeAbbrevDec) < NT_rank (mkNT nDecl)`
            by simp[NT_rank_def] >>
          first_x_assum (erule strip_assume_tac) >>
          dsimp[cmlG_FDOM, cmlG_applied]))
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
          asm_match
            `peg_eval cmlPEG (i1,nt (mkNT nPattern) I) (SOME(equalsT::i2,r))` >>
          `LENGTH i1 < SUC (LENGTH i1)` by decide_tac >>
          first_assum (erule strip_assume_tac) >> rveq >> simp[] >>
          `LENGTH (equalsT::i2) ≤ LENGTH i1`
            by metis_tac[peg_eval_suffix',
                         DECIDE``x≤y ⇔ x = y ∨ x < y:num``] >> fs[]>>
          `LENGTH i2 < SUC (LENGTH i1)` by decide_tac >>
          metis_tac[]) >>
      dsimp[] >> csimp[] >> metis_tac[DECIDE``x<SUC x``])
  >- (print_tac "nPtuple" >> strip_tac >> rveq >>
      dsimp[cmlG_applied, cmlG_FDOM] >> lrresolve X (K true) mp_tac>>
      simp[] >> strip_tac >> rveq >> simp[])
  >- (print_tac "nPatternList" >> strip_tac >> rveq >>
      TRY(qpat_x_assum`CommaT = FST _`(assume_tac o SYM) >> fs[]) >>
      simp[cmlG_FDOM, cmlG_applied] >>
      `NT_rank (mkNT nPattern) < NT_rank (mkNT nPatternList)`
        by simp[NT_rank_def] >>
      first_x_assum (erule mp_tac) >> strip_tac >> rveq >> simp[] >>
      imp_res_tac length_no_greater >> fs[] >>
      fs[MAP_EQ_APPEND, MAP_EQ_CONS] >>
      lrresolve X (free_in ``nPatternList``) mp_tac >> simp[] >>
      strip_tac >> rveq >> dsimp[] >> rfs[PAIR_MAP])
  >- (print_tac "nPattern" >> strip_tac >> rveq >>
      `NT_rank (mkNT nPcons) < NT_rank (mkNT nPattern)` by simp[NT_rank_def] >>
      simp[cmlG_FDOM, cmlG_applied]
      >- (dsimp[APPEND_EQ_CONS] >> csimp[] >>
          first_x_assum (erule mp_tac) >> strip_tac >> rveq >> simp[] >>
          fs[MAP_EQ_APPEND] >> rveq >> dsimp[] >> fs[] >>
          rename1`peg_eval _ (inp2, nt (mkNT nType) I)` >>
          first_x_assum (qspecl_then [`mkNT nType`, `inp2`] mp_tac) >>
          imp_res_tac length_no_greater \\ fs[] >>
          simp[] >> metis_tac[])
      >- (dsimp[MAP_EQ_CONS] >> disj1_tac >>
          first_x_assum (erule mp_tac) >> strip_tac >> rveq >> simp[])
      >- (dsimp[MAP_EQ_CONS] >> disj1_tac >>
          first_x_assum (erule mp_tac) >> strip_tac >> rveq >> simp[]))
  >- (print_tac "nPcons" >>
      `NT_rank (mkNT nPapp) < NT_rank (mkNT nPcons)`
        by simp[NT_rank_def] >> strip_tac >> rveq >>
      simp[cmlG_applied, cmlG_FDOM]
      >- (lrresolve KEEP (K true) mp_tac >> rpt kill_asm_guard >>
          strip_tac >> rveq >> simp[MAP_EQ_CONS] >> dsimp[] >>
          csimp[] >>
          imp_res_tac length_no_greater >> fs[GSYM CONJ_ASSOC] >>
          rpt (loseC ``NT_rank``) >> lrresolve X (K true) mp_tac >>
          simp[] >> metis_tac[])
      >- (lrresolve X (K true) mp_tac >> rpt kill_asm_guard >>
          strip_tac >> rveq >> simp[]) >>
      lrresolve X (K true) mp_tac >> rpt kill_asm_guard >>
      strip_tac >> rveq >> simp[])
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
      simp[])
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
      >- (simp[cmlG_FDOM, cmlG_applied] >> asm_match `isInt (FST h)` >>
          Cases_on `FST h` >> fs[])
      >- (simp[cmlG_FDOM, cmlG_applied] >> asm_match `isString (FST h)` >>
          Cases_on `FST h` >> fs[])
      >- (simp[cmlG_FDOM, cmlG_applied] >> asm_match `isCharT (FST h)` >>
          Cases_on `FST h` >> fs[])
      >- (first_x_assum (erule mp_tac) >> strip_tac >> rveq >>
          dsimp[cmlG_applied, cmlG_FDOM])
      >- simp[cmlG_FDOM, cmlG_applied]
      >- (simp[cmlG_FDOM, cmlG_applied] >>
          lrresolve KEEP (K true) mp_tac >> kill_asm_guard >>
          ASM_REWRITE_TAC [] >> strip_tac >> rveq >> dsimp[])
      >- dsimp[cmlG_applied, cmlG_FDOM]
      >- (simp[cmlG_FDOM, cmlG_applied] >>
          qpat_x_assum `OpT = FST _` (ASSUME_TAC o SYM) >> dsimp[] >>
          csimp[] >> fs[] >> metis_tac[DECIDE ``x < SUC x``])
      >- (fs[] >> qpat_x_assum `OpT = FST _` (ASSUME_TAC o SYM) >> rveq >>
          fs[])
      >- (fs[] >> qpat_x_assum `OpT = FST _` (ASSUME_TAC o SYM) >> rveq >>
          fs[]))
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
      `∀x:mlptree.
         NN nDtypeCons = ptree_head x ⇔ ptree_head x = NN nDtypeCons`
        by simp[EQ_SYM_EQ] >>
      pop_assum (fn th => simp[th]) >>
      first_x_assum (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[DISJ_IMP_THM, FORALL_AND_THM, peg_eval_tok_SOME, pegsym_to_sym_def,
           mktokLf_def, cmlG_applied, cmlG_FDOM, SUBSET_DEF] >>
      (peg0_nTypeName |> Q.INST[`f` |-> `I`] |> assume_tac) >>
      erule mp_tac (GEN_ALL not_peg0_LENGTH_decreases)>>
      simp[] >> rw[])
  >- (print_tac "nTypeDec" >> simp[peg_TypeDec_def] >> strip_tac >> rveq >>
      dsimp[cmlG_FDOM, cmlG_applied, mktokLf_def, MAP_EQ_SING] >> csimp[] >>
      fs[] >> pop_assum (mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[pegsym_to_sym_def, cmlG_applied, cmlG_FDOM, SUBSET_DEF,
           DISJ_IMP_THM, FORALL_AND_THM, EXISTS_PROD] >>
      dsimp[ptree_list_loc_def])
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
          qpat_x_assum `isTyvarT HH` mp_tac >> Cases_on `HH` >> simp[])
      >- (rename [`LparT = FST sometok`] >> Cases_on `sometok` >>
          fs[] >> rveq >> fs[])
      >- (rename [`LparT = FST sometok`] >> Cases_on `sometok` >>
          fs[] >> rveq >> fs[]) >>
      rename [`LparT = FST sometok`] >> Cases_on `sometok` >>
      fs[] >> rveq >> fs[])
  >- (print_tac "nPType" >>
      `NT_rank (mkNT nDType) < NT_rank (mkNT nPType)` by simp[NT_rank_def] >>
      strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM]
      >- (first_x_assum (erule mp_tac) >>
          simp[MAP_EQ_APPEND, MAP_EQ_CONS] >>
          strip_tac >> rveq >> lrresolve X (free_in ``nPType``) mp_tac >>
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
      >- (first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          simp[NT_rank_def] >> strip_tac >> rveq >> simp[])
      >- (asm_match `isLongidT (FST h)` >> Cases_on `FST h` >> fs[]))
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
      >- (lrresolve X (K true) mp_tac >> simp[] >> strip_tac >> rveq >>
          dsimp[])
      >- (lrresolve KEEP (free_in ``nTypeList2``) mp_tac >>
          rpt kill_asm_guard >> strip_tac >> rveq >> dsimp[] >>
          imp_res_tac length_no_greater >>
          lrresolve X (free_in ``nTyOp``) mp_tac >> fs[] >> simp[] >>
          strip_tac >> rveq >> dsimp[])
      >- (asm_match `isTyvarT h` >> Cases_on`h` >> fs[])
      >- (`NT_rank (mkNT nTyOp) < NT_rank (mkNT nTbase)` by simp[NT_rank_def] >>
          first_x_assum (erule mp_tac) >> strip_tac >> rveq >> simp[])
      >- (lrresolve KEEP (free_in ``nTypeList2``) mp_tac >>
          rpt kill_asm_guard >> strip_tac >> rveq >> simp[] >>
          imp_res_tac length_no_greater >> fs[] >>
          lrresolve X (free_in ``nTyOp``) mp_tac >> simp[] >>
          strip_tac >> rveq >> dsimp[]) >>
      lrresolve KEEP (free_in ``nTypeList2``) mp_tac >>
      rpt kill_asm_guard >> strip_tac >> rveq >> simp[] >>
      imp_res_tac length_no_greater >> fs[] >>
      lrresolve X (free_in ``nTyOp``) mp_tac >> simp[] >>
      strip_tac >> rveq >> dsimp[])
  >- (print_tac "nDType" >> strip_tac >> rveq >> simp[] >>
      `NT_rank (mkNT nTbase) < NT_rank (mkNT nDType)`
        by simp[NT_rank_def] >>
      first_x_assum (erule mp_tac) >>
      disch_then (qxchl [`base_pt`] strip_assume_tac) >> rveq >> simp[] >>
      erule strip_assume_tac
        (MATCH_MP not_peg0_LENGTH_decreases peg0_nTbase) >>
      qpat_x_assum `peg_eval cmlPEG (II, rpt XX FF) YY` mp_tac >>
      simp[peg_eval_rpt] >> disch_then (qxchl [`tyops`] strip_assume_tac) >>
      rveq >> simp[] >>
      asm_match `peg_eval_list cmlPEG (i1, nt (mkNT nTyOp) I) (i,tyops)`>>
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
      map_every qid_spec_tac [`acc`, `i2`, `i`, `tyops`] >> Induct
      >- (simp[Once peg_eval_cases] >>
          simp[cmlG_FDOM, cmlG_applied]) >>
      map_every qx_gen_tac [`tyop`, `i`, `i2`, `acc`] >>
      simp[Once peg_eval_cases] >> ntac 3 strip_tac >>
      disch_then (qxchl [`i3`] strip_assume_tac) >>
      first_x_assum (erule mp_tac) >>
      disch_then (qxchl [`tyop_pt2`] strip_assume_tac) >> rveq >>
      simp[] >>
      `LENGTH i3 < LENGTH i2`
        by metis_tac[not_peg0_LENGTH_decreases, peg0_nTyOp] >>
      `LENGTH i3 < LENGTH i0` by decide_tac >>
      first_x_assum
        (qspecl_then [`i`, `i3`, `mkNd (mkNT nDType) [acc; tyop_pt2]`]
                     mp_tac)>>
      simp[cmlG_applied, cmlG_FDOM, DISJ_IMP_THM, FORALL_AND_THM])
  >- (print_tac "nType" >> simp[peg_eval_choice] >>
      `NT_rank (mkNT nPType) < NT_rank (mkNT nType)` by simp[NT_rank_def] >>
      strip_tac >> rveq >> simp[]
      >- (first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
          fs[MAP_EQ_CONS, MAP_EQ_APPEND] >> rveq >>
          lrresolve X (free_in ``nType``) mp_tac >>
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
            cmlG_applied, cmlG_FDOM, EXISTS_PROD] >>
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
  >- (print_tac "nE'" >> strip_tac >> rveq >> simp[] >> fs[]
      >- ((* raise case *)
          loseC ``NT_rank`` >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          simp[] >> strip_tac >> rveq >> dsimp[cmlG_FDOM, cmlG_applied])
      >- ((* ElogicOR case *)
          loseC ``LENGTH`` >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          simp[NT_rank_def] >> strip_tac >> rveq >>
          dsimp[cmlG_FDOM, cmlG_applied])
      >- ((* if-then-else case *) loseC ``NT_rank`` >>
          rename [`IfT = FST hdtoken`] >> Cases_on `hdtoken` >> fs[] >> rveq >>
          rename [`ThenT = FST hdtoken`] >> Cases_on `hdtoken` >> fs[] >>
          rveq >>
          first_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o
                         assert (free_in ``ThenT``) o concl)) >>
          rpt kill_asm_guard >> strip_tac >> rveq >> simp[] >>
          first_assum (assume_tac o MATCH_MP length_no_greater o
                       assert (free_in ``ThenT`` o concl)) >> fs[] >>
          rename [`ElseT = FST hdtoken`] >> Cases_on `hdtoken` >> fs[] >>
          rveq >>
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
      >- ((* bogus raise ElogicOR case *)
          loseC ``LENGTH`` >> first_x_assum (fn patth =>
          first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          simp[NT_rank_def] >> strip_tac >> rveq >>
          simp[cmlG_applied, cmlG_FDOM]) >>
      (* even more bogus contradiction *)
      rveq >> rename [`RaiseT = FST hdtok`, `IfT = FST hdtok`] >>
      Cases_on `hdtok` >> fs[] >> rveq >> fs[])
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
          qpat_x_assum `peg_eval cmlPEG X (SOME((ThenT,_)::Y,Z))` (K ALL_TAC) >>
          qpat_x_assum `peg_eval cmlPEG X (SOME((ElseT,_)::Y,Z))` (K ALL_TAC) >>
          loseC ``NT_rank`` >>
          first_x_assum (fn patth =>
            first_assum (mp_tac o PART_MATCH (lhand o rand) patth o concl)) >>
          simp[] >> metis_tac[])
      >- ((* fn x => e case *) loseC ``NT_rank`` >>
          rpt (qpat_x_assum `peg_eval G X NONE` (K ALL_TAC)) >>
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
          rpt (qpat_x_assum `peg_eval G X NONE` (K ALL_TAC)) >>
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
           FORALL_AND_THM, SUBSET_DEF, EXISTS_PROD] >> dsimp[NT_rank_def])
  >- (print_tac "nElogicAND" >> simp[EXISTS_PROD] >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[cmlG_applied, cmlG_FDOM, pegsym_to_sym_def, DISJ_IMP_THM,
           FORALL_AND_THM, SUBSET_DEF, EXISTS_PROD] >> dsimp[NT_rank_def])
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
           FORALL_AND_THM, SUBSET_DEF] >> dsimp[NT_rank_def, EXISTS_PROD])
  >- (print_tac "nEcomp" >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[cmlG_applied, cmlG_FDOM, pegsym_to_sym_def, DISJ_IMP_THM,
           FORALL_AND_THM, SUBSET_DEF] >> dsimp[NT_rank_def, EXISTS_PROD])
  >- (print_tac "nErel" >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[cmlG_applied, cmlG_FDOM, pegsym_to_sym_def, DISJ_IMP_THM,
           FORALL_AND_THM, SUBSET_DEF] >> dsimp[NT_rank_def, EXISTS_PROD])
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
           FORALL_AND_THM, SUBSET_DEF] >> dsimp[NT_rank_def, EXISTS_PROD])
  >- (print_tac "nEmult" >>
      disch_then (match_mp_tac o MATCH_MP peg_linfix_correct_lemma) >>
      simp[cmlG_applied, cmlG_FDOM, pegsym_to_sym_def, DISJ_IMP_THM,
           FORALL_AND_THM, SUBSET_DEF] >> simp[NT_rank_def, EXISTS_PROD])
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
      rpt (qpat_x_assum `peg_eval G X NONE` (K ALL_TAC))
      >- (`NT_rank (mkNT nEliteral) < NT_rank (mkNT nEbase)`
            by simp[NT_rank_def] >>
          first_x_assum (pop_assum o mp_then Any mp_tac) >>
          disch_then (IMP_RES_THEN strip_assume_tac) >> rveq >> simp[])
      >- (* () *) dsimp[]
      >- ((* peg_EbaseParen 1 *)
          IMP_RES_THEN match_mp_tac peg_EbaseParen_sound >> simp[])
      >- ((* [ elist1 ] *)
          rpt (loseC ``NT_rank``) >>
          lrresolve KEEP (K true) mp_tac >> rpt kill_asm_guard >>
          strip_tac >> rveq >> dsimp[])
      >- ((* [ ] *) dsimp[])
      >- ((* "let" ... "in" ... "end" case *)
          rpt (loseC ``NT_rank``) >>
          lrresolve KEEP (free_in ``nLetDecs``) mp_tac >>
          rpt kill_asm_guard >> strip_tac >> rveq >> dsimp[] >>
          first_x_assum (assume_tac o MATCH_MP length_no_greater o
                         assert (free_in ``nLetDecs`` o concl)) >> fs[] >>
          lrresolve X (K true) mp_tac >> simp[] >>
          strip_tac >> rveq >> dsimp[])
      >- ((* FQV *) first_x_assum (erule strip_assume_tac) >> rveq >> simp[])
      >- ((* nCons *)first_x_assum (erule strip_assume_tac) >> rveq >> simp[])
      >- ((* nOpID *)
          rpt (loseC ``NT_rank``) >> lrresolve X (free_in ``nOpID``) mp_tac >>
          simp[] >> strip_tac >> rveq >> dsimp[]) >>
      IMP_RES_THEN mp_tac peg_EbaseParen_sound >> simp[])
  >- (print_tac "nEliteral" >> strip_tac >> rveq >>
      simp[cmlG_applied, cmlG_FDOM] >> rename [`tk = StringT _`] >>
      Cases_on `tk` >> fs[])
  >- (print_tac "nOpID" >> strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM] >>
      fs[] >> rveq >> fs[PAIR_MAP])
  >- (print_tac "nCompOps">> strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM])
  >- (print_tac "nListOps">> strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM])
  >- (print_tac "nRelOps" >> dsimp[EXISTS_PROD] >> strip_tac >> rveq >>
      simp[cmlG_applied, cmlG_FDOM])
  >- (print_tac "nAddOps" >> strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM])
  >- (print_tac "nMultOps">> strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM])
  >- (print_tac "nElist1" >>
      `NT_rank (mkNT nE) < NT_rank (mkNT nElist1)`
        by simp[NT_rank_def] >> strip_tac >> rveq
      >- (first_x_assum (erule mp_tac) >> strip_tac >> rveq >>
          lrresolve X (free_in ``nElist1``) mp_tac >> simp[] >>
          IMP_RES_TAC length_no_greater >> fs[] >> simp[] >> strip_tac >>
          rveq >> dsimp[cmlG_FDOM, cmlG_applied])
      >- (first_x_assum (erule mp_tac) >> dsimp[cmlG_applied, cmlG_FDOM]) >>
      first_x_assum (erule mp_tac) >> dsimp[cmlG_FDOM, cmlG_applied])
  >- (print_tac "nEapp" >> simp[peg_eval_choice] >>
      strip_tac >> rpt (qpat_x_assum `peg_eval X Y NONE` (K ALL_TAC)) >>
      rveq >> simp[] >>
      `NT_rank (mkNT nEbase) < NT_rank (mkNT nEapp)` by simp[NT_rank_def]>>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      erule assume_tac
        (MATCH_MP not_peg0_LENGTH_decreases peg0_nEbase |> GEN_ALL) >>
      asm_match `peg_eval cmlPEG (i0, nt (mkNT nEbase) I) (SOME(i1,[pt]))`>>
      asm_match
        `peg_eval cmlPEG (i1,rpt(nt(mkNT nEbase) I) FLAT) (SOME(i,r))` >>
      qpat_x_assum `peg_eval G (i1, rpt X R) Y` mp_tac >>
      simp[peg_eval_rpt] >> disch_then (qxchl [`pts`] strip_assume_tac) >>
      rveq >>
      `∃acc. real_fringe pt = FLAT (MAP real_fringe acc) ∧
             [pt] = acc ∧ MAP ptree_head acc ∈ cmlG.rules ' (mkNT nEapp) ∧
             (∀pt. MEM pt acc ⇒ valid_lptree cmlG pt)`
        by simp[cmlG_applied, cmlG_FDOM] >>
      ntac 2 (pop_assum mp_tac) >> ntac 2 (pop_assum SUBST1_TAC) >>
      Q.UNDISCH_THEN `LENGTH i1 < LENGTH i0` mp_tac >>
      qpat_x_assum `peg_eval_list X Y Z` mp_tac >>
      map_every qid_spec_tac [`i`, `i1`, `acc`, `pts`] >> Induct
      >- simp[Once peg_eval_cases, cmlG_FDOM] >>
      simp[Once peg_eval_cases] >>
      map_every qx_gen_tac [`pt'`, `acc`, `i2`, `i`] >>
      disch_then (qxchl [`i3`] strip_assume_tac) >>
      ntac 3 strip_tac >>
      lrresolve X (free_in ``pt':mlptree list``) mp_tac >>
      rpt kill_asm_guard >> disch_then (qxchl [`ebpt`] strip_assume_tac) >>
      rveq >> simp[] >>
      first_x_assum (assume_tac o MATCH_MP length_no_greater o
                     assert (free_in ``ebpt:mlptree`` o concl)) >>
      simp[] >>
      first_x_assum
        (qspecl_then [`[mkNd (mkNT nEapp) acc; ebpt]`, `i3`, `i`]
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
