open HolKernel Parse boolLib bossLib

open lcsymtacs boolSimps
open gramTheory
open NTpropertiesTheory
open pred_setTheory

open mmlvalidTheory

fun dsimp thl = asm_simp_tac (srw_ss() ++ DNF_ss) thl

fun qispl_then [] ttac = ttac
  | qispl_then (q::qs) ttac = Q.ISPEC_THEN q (qispl_then qs ttac)
fun qxchl [] ttac = ttac
  | qxchl (q::qs) ttac = Q.X_CHOOSE_THEN q (qxchl qs ttac)
val rveq = rpt BasicProvers.VAR_EQ_TAC

val MAP_EQ_SING = grammarTheory.MAP_EQ_SING
val APPEND_EQ_SING' = CONV_RULE (LAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))
                                listTheory.APPEND_EQ_SING
val _ = augment_srw_ss [rewrites [APPEND_EQ_SING']]

val _ = new_theory "gramProps"

val mmlvalid_not_INR = store_thm(
  "mmlvalid_not_INR",
  ``mmlvalid pt ∧ ptree_fringe pt = MAP TOK i ⇒ ptree_head pt ≠ NT (INR n)``,
  Cases_on `pt` >>
  dsimp[MAP_EQ_SING, mmlvalid_thm] >> rpt strip_tac >> rw[] >>
  fs[mml_okrule_eval_th])

val NT_rank_def = Define`
  NT_rank N =
    case N of
      | INR _ => 0n
      | INL n =>
        if n = nElist1                 then 15
        else if n = nE                 then 14
        else if n = nEhandle           then 13
        else if n = nElogicOR          then 12
        else if n = nElogicAND         then 11
        else if n = nEtyped            then 10
        else if n = nEbefore           then  9
        else if n = nEcomp             then  8
        else if n = nErel              then  7
        else if n = nEadd              then  6
        else if n = nEmult             then  5
        else if n = nEapp              then  4
        else if n = nEbase             then  3
        else if n = nFQV               then  2
        else if n = nV                 then  1
        else if n = nVlist1            then  2
        else if n = nDtypeCons         then  3
        else if n = nDconstructor      then  2
        else if n = nConstructorName   then  2
        else if n = nUQConstructorName then  1
        else if n = nTypeList          then  5
        else if n = nType              then  4
        else if n = nStarTypesP        then  5
        else if n = nStarTypes         then  4
        else if n = nDType             then  3
        else if n = nTyOp              then  2
        else if n = nTypeName          then  2
        else if n = nUQTyOp            then  1
        else 0
`

val MAP_EQ_CONS = store_thm(
  "MAP_EQ_CONS",
  ``(MAP f l = h::t) ⇔ ∃e es. l = e::es ∧ f e = h ∧ MAP f es = t``,
  Cases_on `l` >> simp[])


val mmlG_applied = let
  val cs = TypeBase.constructors_of ``:MMLnonT``
  fun mkrule c = let
    val t = ``mmlG.rules ' (mkNT ^c)``
  in
    SIMP_CONV (srw_ss()) [mmlG_def, finite_mapTheory.FAPPLY_FUPDATE_THM] t
  end
in
  map mkrule cs
end

val mmlG_FDOM = SIMP_CONV (srw_ss()) [mmlG_def] ``FDOM mmlG.rules``

val paireq = prove(
  ``(x,y) = z ⇔ x = FST z ∧ y = SND z``, Cases_on `z` >> simp[])

val GSPEC_INTER = prove(
  ``GSPEC f ∩ Q =
    GSPEC (S ($, o FST o f) (S ($/\ o SND o f) (Q o FST o f)))``,
  simp[GSPECIFICATION, EXTENSION, SPECIFICATION] >> qx_gen_tac `e` >>
  simp[paireq] >> metis_tac[])

val RIGHT_INTER_OVER_UNION = prove(
  ``(a ∪ b) ∩ c = (a ∩ c) ∪ (b ∩ c)``,
  simp[EXTENSION] >> metis_tac[]);

val GSPEC_applied = prove(
  ``GSPEC f x ⇔ x IN GSPEC f``,
  simp[SPECIFICATION])

val c1 = Cong (DECIDE ``(p = p') ==> ((p /\ q) = (p' /\ q))``)
val condc =
    Cong (EQT_ELIM
            (SIMP_CONV bool_ss []
              ``(g = g') ==>
                ((if g then t else e) = (if g' then t else e))``))

val nullconv =
    SIMP_CONV (srw_ss()) [nullableML_EQN, nullableML_def] THENC
    SIMP_CONV (srw_ss())
       ([GSPEC_INTER,RIGHT_INTER_OVER_UNION,combinTheory.o_ABS_R,
         combinTheory.S_ABS_R, combinTheory.S_ABS_L, GSPEC_applied,
         pairTheory.o_UNCURRY_R, pairTheory.S_UNCURRY_R, INSERT_INTER,
         nullableML_def, c1, condc, mmlG_FDOM] @ mmlG_applied);

fun prove_nullable t = let
  val th = nullconv ``nullableNT mmlG (mkNT ^t)``
in
  EQT_ELIM th handle HOL_ERR _ => EQF_ELIM th
end
val nullable_V = prove_nullable ``nV``
val nullable_Vlist1 = prove_nullable ``nVlist1``
val nullable_UQTyOp = prove_nullable ``nUQTyOp``

val len_assum =
    first_x_assum
      (MATCH_MP_TAC o
       assert (Lib.can
                 (find_term (same_const listSyntax.length_tm) o concl)))

val rank_assum =
    first_x_assum
      (MATCH_MP_TAC o
       assert (Lib.can
                 (find_term (same_const ``NT_rank``) o concl)))

val fringe_lengths_def = Define`
  fringe_lengths G sf = { LENGTH i | derives G sf (MAP TOK i) }
`

val RTC_R_I = relationTheory.RTC_RULES |> SPEC_ALL |> CONJUNCT2 |> GEN_ALL
val fringe_length_ptree = store_thm(
  "fringe_length_ptree",
  ``∀G i pt. ptree_fringe pt = MAP TOK i ∧ valid_ptree G pt ⇒
           LENGTH i ∈ fringe_lengths G [ptree_head pt]``,
  ntac 2 gen_tac >>
  HO_MATCH_MP_TAC grammarTheory.ptree_ind >> dsimp[MAP_EQ_SING] >>
  conj_tac
  >- (simp[fringe_lengths_def] >> rpt strip_tac >> qexists_tac `i` >>
      simp[]) >>
  map_every qx_gen_tac [`subs`, `N`] >> rpt strip_tac >>
  simp[fringe_lengths_def] >> qexists_tac `i` >> simp[] >>
  qabbrev_tac `pt = Nd N subs` >>
  `NT N = ptree_head pt` by simp[Abbr`pt`] >>
  `MAP TOK i = ptree_fringe pt` by simp[Abbr`pt`] >> simp[] >>
  match_mp_tac grammarTheory.valid_ptree_derive >> simp[Abbr`pt`]);

val derives_singleTOK = store_thm(
  "derives_singleTOK",
  ``derives G [TOK t] l ⇔ (l = [TOK t])``,
  simp[Once relationTheory.RTC_CASES1, grammarTheory.derive_def] >>
  metis_tac[]);
val _ = export_rewrites ["derives_singleTOK"]

val fringe_lengths_V = store_thm(
  "fringe_lengths_V",
  ``fringe_lengths mmlG [NT (mkNT nV)] = {1}``,
  simp[fringe_lengths_def] >>
  simp[Once relationTheory.RTC_CASES1, MAP_EQ_SING, mmlG_FDOM] >>
  dsimp(MAP_EQ_SING::mmlG_applied) >>
  simp[EXTENSION, EQ_IMP_THM] >> qx_gen_tac `t` >> rpt strip_tac >>
  fs[] >> qexists_tac `[AlphaT "foo"]` >>
  simp[stringTheory.isUpper_def]);

val mkelim_tac =
  gen_tac >> Cases_on `pt` >> simp[mmlvalid_def] >> rw[] >>
  fs(mmlG_FDOM::mmlG_applied) >> Cases_on `l` >> fs[] >>
  Cases_on `h` >> fs[]
fun mkelim_th t = prove(
  ``∀pt. ptree_head pt = NN ^t ⇒ mmlvalid pt ⇒
         pt = Lf (NN ^t) ∨ ∃t. pt = Nd (mkNT ^t) [Lf (TOK t)]``,
  mkelim_tac)

val elimV_thm = mkelim_th ``nV``
val elimUQTyop_thm = mkelim_th ``nUQTyOp``

fun elim_tac th q = let
  fun c1 eqth = let
    val th' = MATCH_MP th eqth handle HOL_ERR _ => MATCH_MP th (SYM eqth)
  in
    first_assum (fn mmlvth => mp_tac (MATCH_MP th' mmlvth))
  end
in
  first_assum c1 >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac
                               (qxchl [q] assume_tac)) >>
  fs[MAP_EQ_SING] >> rveq
end

val elimV_tac = elim_tac elimV_thm

val nullable_fringe_lengths = store_thm(
  "nullable_fringe_lengths",
  ``nullable G sf ⇔ 0 ∈ fringe_lengths G sf``,
  simp[NTpropertiesTheory.nullable_def, fringe_lengths_def,
       listTheory.LENGTH_NIL_SYM]);

fun asm_match q = Q.MATCH_ASSUM_ABBREV_TAC q >>
                  REPEAT (POP_ASSUM (K ALL_TAC o
                                     assert (same_const ``Abbrev`` o
                                             rator o concl)))

val LENGTH_EQ_1 = prove(
  ``LENGTH x = 1 ⇔ ∃e. x = [e]``,
  Cases_on `x` >> simp[listTheory.LENGTH_NIL])

val vlist1_cross_tac =
    elimV_tac `vt1` >> fs[] >>
    TRY (elimV_tac `vt2`) >> fs[] >>
    asm_match `ptree_fringe vlt = []` >>
    qispl_then [`mmlG`] mp_tac fringe_length_ptree >>
    disch_then (qspecl_then [`[]`, `vlt`] mp_tac) >>
    simp[SYM nullable_fringe_lengths, mmlvalid_SYM] >>
    metis_tac [nullable_Vlist1]

val mmlGNIL =
    fringe_length_ptree
      |> ISPEC ``mmlG`` |> Q.SPEC `[]`
      |> SIMP_RULE (srw_ss()) [SYM nullable_fringe_lengths,
                               GSYM AND_IMP_INTRO, mmlvalid_SYM]

val head_TOK = prove(
  ``∀pt t. ptree_head pt = TOK t ⇒ mmlvalid pt ⇒ pt = Lf (TOK t)``,
  Cases >> simp[]);

fun erule k th = let
  fun c th = let
    val (vs, body) = strip_forall (concl th)
  in
    if is_imp body then
      first_assum (c o MATCH_MP th)
    else k th
  end
in
  c th
end

(*
val unambiguous = store_thm(
  "unambiguous",
  ``∀i N p1 p2.
      valid_ptree mmlG p1 ∧ ptree_fringe p1 = MAP TOK i ∧
      ptree_head p1 = NT N ∧
      valid_ptree mmlG p2 ∧ ptree_fringe p2 = MAP TOK i ∧
      ptree_head p2 = NT N ⇒
      p1 = p2``,
  ntac 2 gen_tac >> `∃iN. iN = (i,N)` by simp[] >> pop_assum mp_tac >>
  map_every qid_spec_tac [`N`, `i`, `iN`] >>
  Q.ISPEC_THEN
    `measure (LENGTH:token list -> num) LEX measure (NT_rank: NT -> num)`
    (HO_MATCH_MP_TAC o SIMP_RULE (srw_ss()) [pairTheory.WF_LEX])
    relationTheory.WF_INDUCTION_THM >>
  dsimp[pairTheory.LEX_DEF, AND_IMP_INTRO, mmlvalid_SYM] >>
  rpt strip_tac >>
  `(∃x. N = INR x) ∨ ∃n. N = INL n` by (Cases_on `N` >> simp[])
  >- metis_tac[mmlvalid_not_INR] >> rw[] >>
  Cases_on `n`
  >- ((* nVlist1 *) Cases_on `p1` >> fs[MAP_EQ_SING] >> rw[] >>
      Cases_on `p2` >>
      fs[MAP_EQ_SING, mmlvalid_thm, mml_okrule_eval_th, MAP_EQ_CONS] >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[grammarTheory.MAP_EQ_APPEND]
      >- (elimV_tac `vt1` >> fs[MAP_EQ_SING] >> rveq >>
          elimV_tac `vt2` >> fs[MAP_EQ_SING] >> rveq >>
          len_assum >> simp[] >> metis_tac[DECIDE ``x < x + 1n``])
      >- vlist1_cross_tac >- vlist1_cross_tac >>
      elimV_tac `vtok` >> elimV_tac `vtok2`)
  >- ((* V *) elimV_tac `vt1` >> elimV_tac `vt2`)
  >- ((* UQTyOp *) elim_tac elimUQTyop_thm `tyt1` >>
      elim_tac elimUQTyop_thm `tyt2`)
  >- ((* nUQConstructorName *)
      elim_tac (mkelim_th ``nUQConstructorName``) `t1` >>
      elim_tac (mkelim_th ``nUQConstructorName``) `t2`)
  >- ((* nTypeName *)
      Cases_on `p1` >> fs[MAP_EQ_SING] >> rw[] >>
      Cases_on `p2` >>
      fs(MAP_EQ_SING::mmlvalid_def::mmlG_FDOM::mmlG_applied) >>
      rveq >> fs[mmlvalid_SYM, MAP_EQ_CONS] >> rveq >>
      fs[DISJ_IMP_THM, FORALL_AND_THM]
      >- (elim_tac elimUQTyop_thm `t1` >> elim_tac elimUQTyop_thm `t2`)
      >- (elim_tac elimUQTyop_thm `t1` >>
          elim_tac elimUQTyop_thm `t2` >> fs[] >>
          imp_res_tac mmlGNIL >> ntac 3 (pop_assum mp_tac) >>
          simp[])
      >- (elim_tac elimUQTyop_thm `t1` >>
          fs[grammarTheory.MAP_EQ_APPEND, MAP_EQ_SING] >>
          elim_tac elimUQTyop_thm `t2` >> fs[] >>
          imp_res_tac mmlGNIL >> pop_assum mp_tac >> simp[])
      >- (elim_tac elimUQTyop_thm `t1` >>
          imp_res_tac mmlGNIL >> ntac 3 (pop_assum mp_tac) >> simp[])
      >- (elim_tac elimUQTyop_thm `t1` >>
          fs[grammarTheory.MAP_EQ_APPEND, MAP_EQ_SING] >> rveq >>
          elim_tac elimUQTyop_thm `t2` >>
          rpt
            (erule SUBST_ALL_TAC head_TOK >> fs[MAP_EQ_SING] >> rveq) >>
          rw[] >> len_assum >> simp[] >>
          metis_tac [DECIDE ``x < x + 3n``])
      >- (rpt
            (erule SUBST_ALL_TAC head_TOK >> fs[MAP_EQ_SING] >> rveq) >>
          pop_assum (assume_tac o SYM) >> fs[])
      >- (erule SUBST_ALL_TAC head_TOK >>
          elim_tac elimUQTyop_thm `t` >> erule mp_tac mmlGNIL >>
          simp[nullable_UQTyOp])
      >- (rpt
            (erule SUBST_ALL_TAC head_TOK >> fs[MAP_EQ_SING]) >>
          pop_assum (assume_tac o SYM) >> fs[]) >>
      rpt (erule SUBST_ALL_TAC head_TOK >> fs[MAP_EQ_SING]) >>
      pop_assum (assume_tac o SYM) >> fs[] >>
      elim_tac elimUQTyop_thm `t1` >> fs[MAP_EQ_CONS])


*)
val _ = export_theory()
