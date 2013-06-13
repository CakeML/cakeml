open HolKernel Parse boolLib bossLib;

open pred_setTheory
open mmlPEGTheory gramTheory gramPropsTheory
open lcsymtacs boolSimps

val MAP_EQ_SING = grammarTheory.MAP_EQ_SING
val APPEND_ASSOC = listTheory.APPEND_ASSOC

val FDOM_cmlPEG = mmlPEGTheory.FDOM_cmlPEG
val mmlpeg_rules_applied = mmlPEGTheory.mmlpeg_rules_applied

fun loseC c =
    first_x_assum
      (K ALL_TAC o assert (can (find_term (same_const c)) o concl))
fun asm_match q = Q.MATCH_ASSUM_ABBREV_TAC q >>
                  REPEAT (POP_ASSUM (K ALL_TAC o
                                     assert (same_const ``Abbrev`` o
                                             rator o concl)))
fun Store_thm(n,t,tac) = store_thm(n,t,tac) before export_rewrites [n]

fun dsimp thl = asm_simp_tac (srw_ss() ++ DNF_ss) thl
fun asimp thl = asm_simp_tac (srw_ss() ++ ARITH_ss) thl
fun csimp thl = asm_simp_tac (srw_ss() ++ CONJ_ss) thl

fun qispl_then [] ttac = ttac
  | qispl_then (q::qs) ttac = Q.ISPEC_THEN q (qispl_then qs ttac)
fun qxchl [] ttac = ttac
  | qxchl (q::qs) ttac = Q.X_CHOOSE_THEN q (qxchl qs ttac)
val rveq = rpt BasicProvers.VAR_EQ_TAC

fun erule k th = let
  fun c th = let
    val (vs, body) = strip_forall (concl th)
  in
    if is_imp body then
      first_assum (c o MATCH_MP th) ORELSE
      first_assum (c o MATCH_MP th o SYM)
    else k th
  end
  fun is_resolvable th = let
    val (vs, body) = strip_forall (concl th)
  in
    is_imp body
  end
in
  if is_resolvable th then c th else NO_TAC
end




val _ = new_theory "PEG_CFG";

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
  ``¬peg0 G s ∧ peg_eval G (i0, s) (SOME(i,r)) ⇒ LENGTH i < LENGTH i0``,
  strip_tac >> `i ≠ i0` by metis_tac [pegTheory.lemma4_1a] >>
  metis_tac[pegTheory.peg_eval_suffix'])

val pegfail_empty = Store_thm(
  "pegfail_empty",
  ``pegfail G (empty r) = F``,
  simp[Once pegTheory.peg0_cases]);

val peg0_empty = Store_thm(
  "peg0_empty",
  ``peg0 G (empty r) = T``,
  simp[Once pegTheory.peg0_cases]);

val peg0_not = Store_thm(
  "peg0_not",
  ``peg0 G (not s r) ⇔ pegfail G s``,
  simp[Once pegTheory.peg0_cases, SimpLHS]);

val peg0_choice = Store_thm(
  "peg0_choice",
  ``peg0 G (choice s1 s2 f) ⇔ peg0 G s1 ∨ pegfail G s1 ∧ peg0 G s2``,
  simp[Once pegTheory.peg0_cases, SimpLHS]);

val peg0_choicel = Store_thm(
  "peg0_choicel",
  ``(peg0 G (choicel []) = F) ∧
    (peg0 G (choicel (h::t)) ⇔ peg0 G h ∨ pegfail G h ∧ peg0 G (choicel t))``,
  simp[choicel_def])

val peg0_seq = Store_thm(
  "peg0_seq",
  ``peg0 G (seq s1 s2 f) ⇔ peg0 G s1 ∧ peg0 G s2``,
  simp[Once pegTheory.peg0_cases, SimpLHS])

val peg0_pegf = Store_thm(
  "peg0_pegf",
  ``peg0 G (pegf s f) = peg0 G s``,
  simp[pegf_def])

val peg0_seql = Store_thm(
  "peg0_seql",
  ``(peg0 G (seql [] f) ⇔ T) ∧
    (peg0 G (seql (h::t) f) ⇔ peg0 G h ∧ peg0 G (seql t I))``,
  simp[seql_def])

val peg0_tok = Store_thm(
  "peg0_tok",
  ``peg0 G (tok P f) = F``,
  simp[Once pegTheory.peg0_cases])

val peg0_tokeq = Store_thm(
  "peg0_tokeq",
  ``peg0 G (tokeq t) = F``,
  simp[tokeq_def])

val peg0_nStructure = Store_thm(
  "peg0_nStructure",
  ``peg0 mmlPEG (nt (mkNT nStructure) f) = F``,
  simp[Once pegTheory.peg0_cases, mmlpeg_rules_applied, FDOM_cmlPEG]);

val peg0_nTypeDec = Store_thm(
  "peg0_nTypeDec",
  ``peg0 mmlPEG (nt (mkNT nTypeDec) f) = F``,
  simp[Once pegTheory.peg0_cases, mmlpeg_rules_applied, FDOM_cmlPEG,
       peg_TypeDec_def]);

val peg0_nDecl = Store_thm(
  "peg0_nDecl",
  ``peg0 mmlPEG (nt (mkNT nDecl) f) = F``,
  simp[Once pegTheory.peg0_cases, mmlpeg_rules_applied, FDOM_cmlPEG,
       pnt_def])

val peg0_nTopLevelDec = Store_thm(
  "peg0_nTopLevelDec",
  ``¬peg0 mmlPEG (nt (mkNT nTopLevelDec) f)``,
  simp[Once pegTheory.peg0_cases, mmlpeg_rules_applied, FDOM_cmlPEG, pnt_def])

val peg0_nV = Store_thm(
  "peg0_nV",
  ``¬peg0 mmlPEG (nt (mkNT nV) f)``,
  simp[Once pegTheory.peg0_cases, mmlpeg_rules_applied, FDOM_cmlPEG, peg_V_def])

val peg0_nSpecLine = Store_thm(
  "peg0_nSpecLine",
  ``¬peg0 mmlPEG (nt (mkNT nSpecLine) f)``,
  simp[Once pegTheory.peg0_cases, mmlpeg_rules_applied, FDOM_cmlPEG, pnt_def])

val peg0_nLetDec = Store_thm(
  "peg0_nLetDec",
  ``¬peg0 mmlPEG (nt (mkNT nLetDec) f)``,
  simp[Once pegTheory.peg0_cases, mmlpeg_rules_applied, FDOM_cmlPEG, pnt_def])

val peg0_nUQConstructorName = Store_thm(
  "peg0_nUQConstructorName",
  ``¬peg0 mmlPEG (nt (mkNT nUQConstructorName) f)``,
  simp[Once pegTheory.peg0_cases, mmlpeg_rules_applied, FDOM_cmlPEG,
       peg_UQConstructorName_def])

val peg0_nConstructorName = Store_thm(
  "peg0_nConstructorName",
  ``¬peg0 mmlPEG (nt (mkNT nConstructorName) f)``,
  simp[Once pegTheory.peg0_cases, mmlpeg_rules_applied, FDOM_cmlPEG, pnt_def])

val peg0_nPbase = Store_thm(
  "peg0_nPbase",
  ``¬peg0 mmlPEG (nt (mkNT nPbase) f)``,
  simp[Once pegTheory.peg0_cases, mmlpeg_rules_applied, FDOM_cmlPEG, pnt_def]);

val peg0_nPattern = Store_thm(
  "peg0_nPattern",
  ``¬peg0 mmlPEG (nt (mkNT nPattern) f)``,
  simp[Once pegTheory.peg0_cases, mmlpeg_rules_applied, FDOM_cmlPEG, pnt_def])

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

fun print_tac s g = (print ("print_tac: "^s^"\n"); ALL_TAC g)

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
              valid_ptree mmlG pt ∧ ptree_fringe pt ++ MAP TK i = MAP TK i0') ∧
      (∀i pts s.
         s ∈ {sym; sepsym} ⇒
         peg_eval mmlPEG (i0, s) (SOME(i,pts)) ⇒
         ∃pt. pts = [pt] ∧ ptree_head pt ∈ pegsym_to_sym s ∧
              valid_ptree mmlG pt ∧ ptree_fringe pt ++ MAP TK i = MAP TK i0) ∧
      ¬peg0 mmlPEG sym ∧
      UpperN ∈ FDOM mmlG.rules ∧
      {[gsym] | gsym ∈ pegsym_to_sym sym } ⊆ mmlG.rules ' UpperN ∧
      {[NT UpperN; gsep; gsym] |
          gsep ∈ pegsym_to_sym sepsym ∧ gsym ∈ pegsym_to_sym sym } ⊆
        mmlG.rules ' UpperN ⇒
      ∃pt. pts = [pt] ∧ ptree_head pt = NT UpperN ∧ valid_ptree mmlG pt ∧
           ptree_fringe pt ++ MAP TK i = MAP TK i0``,
  rpt strip_tac >> qpat_assum `peg_eval X Y Z` mp_tac >>
  simp[peg_linfix_def, peg_eval_rpt, peg_eval_seq_SOME] >>
  rpt strip_tac >> rveq >>
  asm_match `peg_eval mmlPEG (i0, sym) (SOME(i1,r1))` >>
  first_assum (qspecl_then [`i1`, `r1`, `sym`] mp_tac) >> simp_tac(srw_ss())[]>>
  ASM_REWRITE_TAC[] >> disch_then (qxchl[`rpt1`] strip_assume_tac) >> simp[] >>
  rveq >>
  qpat_assum `peg_eval_list X Y Z` mp_tac >>
  pop_assum (fn th => SUBST1_TAC (SYM th) >> assume_tac th) >>
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
  simp_tac(srw_ss()) [] >> ASM_REWRITE_TAC[] >>
  disch_then (qxchl [`sep_pt`] strip_assume_tac) >> rveq >>
  `LENGTH i2' ≤ LENGTH i1'`
    by metis_tac[pegTheory.peg_eval_suffix',
                 DECIDE``x:num ≤ y ⇔ x = y ∨ x < y``] >>
  `LENGTH i2' < LENGTH i0` by decide_tac >>
  first_x_assum (qspecl_then [`i2'`, `i3'`, `sym_r`, `sym`] mp_tac) >>
  simp_tac(srw_ss()) [] >> ASM_REWRITE_TAC[] >>
  disch_then (qxchl [`sym_pt`] strip_assume_tac) >> rveq >>
  simp[mk_linfix_def] >>
  `LENGTH i3' < LENGTH i2'` by metis_tac[not_peg0_LENGTH_decreases] >>
  `LENGTH i3' ≤ LENGTH i1` by decide_tac >>
  first_x_assum (qspecl_then [`i`, `i3'`, `[Nd UpperN acc; sep_pt; sym_pt]`]
                             mp_tac) >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  `[NT UpperN; ptree_head sep_pt; ptree_head sym_pt] ∈ mmlG.rules ' UpperN`
    by fs[SUBSET_DEF] >>
  simp[] >> strip_tac >>
  rpt (qpat_assum `XX = MAP TK II` (SUBST_ALL_TAC o SYM)) >> simp[]);

(*
val peg_correct = store_thm(
  "peg_correct",
  ``∀N i0 s i pts.
       peg_eval mmlPEG (i0,nt N I) (SOME(i,pts)) ⇒
       ∃pt. pts = [pt] ∧ ptree_head pt = NT N ∧
            valid_ptree mmlG pt ∧
            ptree_fringe pt ++ MAP TOK i = MAP TOK i0``,
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
  simp[mmlPEGTheory.mmlpeg_rules_applied, pnt_def, peg_eval_choicel_CONS,
       tokeq_def]
  >- (print_tac "nREPLTop">>
      simp[peg_eval_seql_CONS, peg_eval_tok_SOME, tokeq_def,
           bindNT_def] >>
      Cases_on `peg_eval mmlPEG (i0, nt (mkNT nE) I) NONE`
      >- (pop_assum (assume_tac o
                     (pegTheory.peg_deterministic |> CONJUNCT1 |> MATCH_MP)) >>
          simp[] >> disch_then (qxchl [`r`] strip_assume_tac) >> rveq >>
          simp[cmlG_applied, cmlG_FDOM, mktokLf_def, MAP_EQ_SING] >> dsimp[] >>
          DISJ1_TAC >> csimp[] >>
          first_x_assum (qspecl_then [`mkNT nTopLevelDec`, `SemicolonT::i`, `r`]
                                     mp_tac) >> simp[NT_rank_def] >>
          metis_tac[]) >>
      rpt strip_tac >>
      dsimp[cmlG_FDOM, cmlG_applied, mktokLf_def, MAP_EQ_SING] >> csimp[]
      >- (DISJ2_TAC >>
          first_x_assum (qspecl_then [`mkNT nE`, `SemicolonT::i`, `rh`]
                                     mp_tac) >> simp[NT_rank_def] >>
          metis_tac[]) >>
      DISJ1_TAC >> csimp[] >>
      first_x_assum (qspecl_then [`mkNT nTopLevelDec`, `SemicolonT::i`, `rh'`]
                                 mp_tac) >> simp[NT_rank_def] >>
      metis_tac[])
  >- (print_tac "nREPLPhrase" >>
      simp[peg_eval_seql_CONS, peg_eval_tok_SOME, tokeq_def, bindNT_def] >>
      Cases_on `peg_eval mmlPEG (i0, nt (mkNT nE) I) NONE`
      >- (pop_assum (assume_tac o
                     (pegTheory.peg_deterministic |> CONJUNCT1 |> MATCH_MP)) >>
          simp[] >> disch_then (qxchl [`r`] strip_assume_tac) >> rveq >>
          simp[cmlG_applied, cmlG_FDOM, mktokLf_def, MAP_EQ_SING] >> dsimp[]>>
          DISJ1_TAC >> csimp[] >>
          first_x_assum
          (qspecl_then [`mkNT nTopLevelDecs`, `SemicolonT::i`, `r`]
                       mp_tac) >> simp[NT_rank_def] >>
          metis_tac[]) >>
      rpt strip_tac >>
      dsimp[cmlG_FDOM, cmlG_applied, mktokLf_def, MAP_EQ_SING] >> csimp[]
      >- (DISJ2_TAC >>
          first_x_assum (qspecl_then [`mkNT nE`, `SemicolonT::i`, `rh`]
                                     mp_tac)>>
          simp[NT_rank_def] >> metis_tac[]) >>
      DISJ1_TAC >>
      first_x_assum (qspecl_then [`mkNT nTopLevelDecs`, `SemicolonT::i`, `rh'`]
                                 mp_tac)>>
      simp[NT_rank_def] >> metis_tac[])
  >- (print_tac "nTopLevelDecs" >>
      qmatch_abbrev_tac `peg_eval mmlPEG (i0, rpt NNN FF) (SOME(i,pts)) ⇒ QQ`>>
      map_every markerLib.UNABBREV_TAC ["NNN", "QQ"] >>
      `(FF [] = [Nd (mkNT nTopLevelDecs) []]) ∧
       ∀h t. FF ([h]::t) = [Nd (mkNT nTopLevelDecs) [h; HD (FF t)]]`
        by simp[Abbr`FF`] >>
      markerLib.RM_ABBREV_TAC "FF" >>
      simp[peg_eval_rpt] >>
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
      dsimp[cmlG_applied, cmlG_FDOM] >> metis_tac[APPEND_ASSOC])
  >- (print_tac "nTopLevelDec" >>
      simp[peg_eval_choicel_CONS, pegf_def, peg_eval_seql_CONS,
           peg_eval_seq_SOME, bindNT_def] >>
      `NT_rank (mkNT nStructure) < NT_rank (mkNT nTopLevelDec) ∧
       NT_rank (mkNT nDecl) < NT_rank (mkNT nTopLevelDec)`
        by simp[NT_rank_def] >>
      strip_tac >>
      first_x_assum (erule mp_tac) >>
      strip_tac >> simp[cmlG_FDOM, cmlG_applied])
  >- (print_tac "nStructure" >>
      simp[peg_eval_seql_CONS, peg_eval_seq_SOME, bindNT_def,
           peg_eval_tok_SOME, mktokLf_def] >> strip_tac >> rveq >>
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
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[] >>
      rpt (qpat_assum `XX = MAP TK YY` (SUBST_ALL_TAC o SYM)) >>
      simp[])
  >- (print_tac "nOptionalSignatureAscription" >>
      simp[peg_eval_seql_CONS, bindNT_def, pegf_def, peg_eval_seq_SOME,
           peg_eval_try, peg_eval_tok_SOME, mktokLf_def] >> strip_tac >>
      rveq >> simp[cmlG_applied, cmlG_FDOM] >> dsimp[] >>
      loseC ``NT_rank`` >> dsimp[MAP_EQ_SING] >> csimp[] >> fs[] >>
      metis_tac [DECIDE ``x < SUC x``])
  >- (print_tac "nSignatureValue" >>
      simp[peg_eval_seql_CONS, bindNT_def, peg_eval_tok_SOME, mktokLf_def] >>
      strip_tac >> rveq >> simp[cmlG_FDOM, cmlG_applied, MAP_EQ_SING] >>
      dsimp[] >> csimp[] >>
      asm_match `peg_eval mmlPEG (slli, nt (mkNT nSpecLineList) I)
                          (SOME (EndT::i, r))` >>
      first_x_assum (qspecl_then [`mkNT nSpecLineList`, `slli`, `EndT::i`, `r`]
                                 mp_tac) >> simp[] >> metis_tac[])
  >- (print_tac "nSpecLineList" >>
      simp[peg_eval_seql_CONS, bindNT_def, peg_eval_tok_SOME, mktokLf_def,
           pegf_def, peg_eval_seq_SOME] >>
      strip_tac >> simp[cmlG_applied, cmlG_FDOM]
      >- (`NT_rank (mkNT nSpecLine) < NT_rank (mkNT nSpecLineList)`
             by simp[NT_rank_def] >>
          first_x_assum (erule mp_tac) >>
          asm_match
            `peg_eval mmlPEG (i0, nt (mkNT nSpecLine) I) (SOME (i1,r))` >>
          `LENGTH i1 < LENGTH i0`
            by metis_tac[not_peg0_LENGTH_decreases, peg0_nSpecLine] >>
          first_x_assum (erule mp_tac) >> rpt strip_tac >> rveq >> fs[] >>
          metis_tac [APPEND_ASSOC])
      >- (dsimp[MAP_EQ_SING] >> csimp[]>>fs[] >> metis_tac[DECIDE``x < SUC x``])
      >> fs[cmlG_FDOM, cmlG_applied, MAP_EQ_SING] >> dsimp[] >> csimp[] >>
          metis_tac[DECIDE``x< SUC x``])
  >- (print_tac "nSpecLine" >>
      simp[peg_eval_seql_CONS, bindNT_def, peg_eval_tok_SOME, mktokLf_def,
           pegf_def, peg_eval_seq_SOME] >>
      strip_tac >> rveq >> fs[cmlG_applied, cmlG_FDOM, peg_eval_TypeDec_wrongtok]
      >- (asm_match
            `peg_eval mmlPEG (i1, nt (mkNT nV) I) (SOME(ColonT::i2,r))` >>
          `LENGTH i1 < SUC (LENGTH i1)` by DECIDE_TAC >>
          first_assum (erule strip_assume_tac) >>
          `LENGTH (ColonT::i2) < LENGTH i1`
            by metis_tac[not_peg0_LENGTH_decreases, peg0_nV] >> fs[] >>
          `LENGTH i2 < SUC(LENGTH i1)` by decide_tac >>
          first_x_assum (erule strip_assume_tac) >> rveq >> dsimp[] >>
          metis_tac[APPEND_ASSOC])
      >- (dsimp[MAP_EQ_SING] >> csimp[] >> metis_tac[DECIDE``x<SUC x``])>>
      `NT_rank (mkNT nTypeDec) < NT_rank (mkNT nSpecLine)`
         by simp[NT_rank_def] >>
      first_x_assum (erule strip_assume_tac) >> rveq >> simp[])
  >- (print_tac "nDecls" >>
      simp[peg_eval_seql_CONS, bindNT_def, peg_eval_tok_SOME, mktokLf_def,
           pegf_def, peg_eval_seq_SOME, peg_eval_tok_SOME] >>
      `NT_rank (mkNT nDecl) < NT_rank (mkNT nDecls)`
        by simp[NT_rank_def] >>
      strip_tac >> rveq >> fs[cmlG_applied, cmlG_FDOM]
      >- (first_x_assum (erule strip_assume_tac) >>
          asm_match `peg_eval mmlPEG (i0,nt (mkNT nDecl) I) (SOME(i1,r))` >>
          dsimp[MAP_EQ_SING] >>
          `LENGTH i1 < LENGTH i0`
            by metis_tac[not_peg0_LENGTH_decreases,peg0_nDecl] >>
          first_x_assum (erule strip_assume_tac) >>
          dsimp[MAP_EQ_SING] >> metis_tac[APPEND_ASSOC])
      >- (dsimp[MAP_EQ_SING] >> csimp[] >> metis_tac[DECIDE``x<SUC x``]) >>
      dsimp[MAP_EQ_SING] >> csimp[] >> metis_tac[DECIDE``x<SUC x``])
  >- (print_tac "nDecl" >>
      simp[peg_eval_seql_CONS, bindNT_def, peg_eval_tok_SOME, mktokLf_def,
           pegf_def] >> rpt strip_tac >> rveq >> fs[peg_eval_TypeDec_wrongtok]
      >- (asm_match `peg_eval mmlPEG (i1, nt (mkNT nPattern) I)
                              (SOME(EqualsT::i2,r))` >>
          `LENGTH i1 < SUC (LENGTH i1)` by decide_tac >>
          first_assum (erule strip_assume_tac) >> rveq >>
          `LENGTH (EqualsT::i2) ≤ LENGTH i1`
            by metis_tac[pegTheory.peg_eval_suffix',
                         DECIDE``x≤y ⇔ x = y ∨ x < y:num``] >> fs[]>>
          `LENGTH i2 < SUC (LENGTH i1)` by decide_tac >>
          first_x_assum (erule strip_assume_tac) >> rveq >>
          simp[cmlG_FDOM, cmlG_applied, MAP_EQ_SING] >> dsimp[] >>
          rpt (qpat_assum `XX = MAP TK II` (SUBST_ALL_TAC o SYM)) >>
          simp[])
      >- (dsimp[cmlG_applied, cmlG_FDOM, MAP_EQ_SING] >> csimp[] >>
          metis_tac[DECIDE ``x<SUC x``]) >>
      `NT_rank (mkNT nTypeDec) < NT_rank (mkNT nDecl)`
        by simp[NT_rank_def] >>
      first_x_assum (erule strip_assume_tac) >>
      dsimp[cmlG_FDOM, cmlG_applied])
  >- (print_tac "nLetDecs" >>
      simp[peg_eval_seql_CONS, bindNT_def, peg_eval_tok_SOME, mktokLf_def,
           pegf_def, peg_eval_seq_SOME] >> rpt strip_tac >> rveq >>
      simp[cmlG_applied, cmlG_FDOM] >> fs[peg_eval_LetDec_wrongtok]
      >- (simp[] >>
          `NT_rank (mkNT nLetDec) < NT_rank (mkNT nLetDecs)`
            by simp[NT_rank_def] >>
          first_x_assum (erule strip_assume_tac) >> rveq >>
          dsimp[cmlG_applied, cmlG_FDOM, MAP_EQ_SING] >> csimp[] >>
          qpat_assum `XX = MAP TK II` (SUBST_ALL_TAC o SYM) >> simp[] >>
          metis_tac[not_peg0_LENGTH_decreases, peg0_nLetDec]) >>
      dsimp[MAP_EQ_SING] >> csimp[] >> metis_tac[DECIDE ``x < SUC x``])
  >- (print_tac "nLetDec" >>
      simp[peg_eval_seql_CONS, peg_eval_tok_SOME, mktokLf_def, bindNT_def] >>
      rpt strip_tac >> rveq >> simp[cmlG_FDOM, cmlG_applied, MAP_EQ_SING] >> fs[]
      >- (dsimp[listTheory.APPEND_EQ_CONS, MAP_EQ_SING] >> csimp[] >>
          asm_match`peg_eval mmlPEG (i1,nt (mkNT nV) I) (SOME(EqualsT::i2,r))` >>
          `LENGTH i1 < SUC (LENGTH i1)` by decide_tac >>
          first_assum (erule strip_assume_tac) >> rveq >> simp[] >>
          qpat_assum `XX = MAP TK II` (SUBST_ALL_TAC o SYM) >> simp[] >>
          `LENGTH (EqualsT::i2) ≤ LENGTH i1`
            by metis_tac[pegTheory.peg_eval_suffix',
                         DECIDE``x≤y ⇔ x = y ∨ x < y:num``] >> fs[]>>
          `LENGTH i2 < SUC (LENGTH i1)` by decide_tac >>
          metis_tac[]) >>
      dsimp[] >> csimp[] >> metis_tac[DECIDE``x<SUC x``])
  >- (print_tac "nPatternList1" >> strip_tac >>
      match_mp_tac (GEN_ALL peg_linfix_correct_lemma) >>
      map_every qexists_tac
        [`nt (mkNT nPattern) I`, `tok ($= CommaT) mktokLf`] >>
      simp[pegsym_to_sym_def] >>
      simp[DISJ_IMP_THM, FORALL_AND_THM, cmlG_applied, cmlG_FDOM, NT_rank_def,
           SUBSET_DEF, EXTENSION, peg_eval_tok_SOME, mktokLf_def,
           pegsym_to_sym_def])
  >- (print_tac "nPatternList2" >>
      simp[peg_eval_seql_CONS, peg_eval_tok_SOME, bindNT_def, mktokLf_def] >>
      strip_tac >> rveq >> simp[cmlG_applied, cmlG_FDOM] >>
      dsimp[listTheory.APPEND_EQ_CONS, MAP_EQ_SING] >> csimp[] >>
      `NT_rank (mkNT nPattern) < NT_rank (mkNT nPatternList2)`
        by simp[NT_rank_def]






*)
val _ = export_theory();
