open HolKernel Parse boolLib bossLib

open lcsymtacs boolSimps
open gramTheory
open NTpropertiesTheory
open pred_setTheory
open parsingPreamble

fun dsimp thl = asm_simp_tac (srw_ss() ++ DNF_ss) thl
fun asimp thl = asm_simp_tac (srw_ss() ++ ARITH_ss) thl

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
in
  c th
end

val MAP_EQ_SING = grammarTheory.MAP_EQ_SING
val APPEND_EQ_SING' = CONV_RULE (LAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))
                                listTheory.APPEND_EQ_SING
val _ = augment_srw_ss [rewrites [APPEND_EQ_SING']]

val _ = new_theory "gramProps"

val NT_rank_def = Define`
  NT_rank N =
    case N of
      | INR _ => 0n
      | INL n =>
        if n = nElist1                 then 16
        else if n = nEseq              then 16
        else if n = nREPLTop           then 16
        else if n = nElist2            then 16
        else if n = nE                 then 15
        else if n = nE'                then 15
        else if n = nEhandle           then 14
        else if n = nElogicOR          then 13
        else if n = nElogicAND         then 12
        else if n = nEtyped            then 11
        else if n = nEbefore           then 10
        else if n = nEcomp             then  9
        else if n = nErel              then  8
        else if n = nElistop           then  7
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
        else if n = nTypeList2         then  8
        else if n = nTypeList1         then  7
        else if n = nType              then  6
        else if n = nPType             then  5
        else if n = nDType             then  4
        else if n = nTbase             then  3
        else if n = nTyOp              then  2
        else if n = nTypeName          then  2
        else if n = nUQTyOp            then  1
        else if n = nTopLevelDecs      then  4
        else if n = nTopLevelDec       then  3
        else if n = nDecls             then  3
        else if n = nStructure         then  2
        else if n = nDecl              then  2
        else if n = nTypeDec           then  1
        else if n = nSpecLineList      then  3
        else if n = nSpecLine          then  2
        else if n = nPtuple            then  2
        else if n = nPbase             then  3
        else if n = nPapp              then  4
        else if n = nPattern           then  5
        else if n = nPatternList       then  6
        else if n = nPEs               then  7
        else if n = nPE                then  6
        else if n = nPE'               then  6
        else if n = nLetDecs           then  2
        else if n = nLetDec            then  1
        else if n = nDtypeDecl         then  3
        else if n = nAndFDecls         then  3
        else if n = nFDecl             then  2
        else if n = nTyVarList         then  2
        else if n = nTyvarN            then  1
        else                                 0
`

val rules_t = ``cmlG.rules``
fun ty2frag ty = let
  open simpLib
  val {convs,rewrs} = TypeBase.simpls_of ty
in
  merge_ss (rewrites rewrs :: map conv_ss convs)
end
val rules = SIMP_CONV (bool_ss ++ ty2frag ``:(α,β)grammar``)
                      [cmlG_def, combinTheory.K_DEF,
                       finite_mapTheory.FUPDATE_LIST_THM] rules_t
val cmlG_applied = let
  val app0 = finite_mapSyntax.fapply_t
  val theta =
      Type.match_type (type_of app0 |> dom_rng |> #1) (type_of rules_t)
  val app = inst theta app0
  val app_rules = AP_TERM app rules
  val sset = bool_ss ++ ty2frag ``:'a + 'b`` ++ ty2frag ``:MMLnonT``
  fun mkrule t =
      (print ("cmlG_applied: " ^ term_to_string t ^"\n");
       AP_THM app_rules ``mkNT ^t``
              |> SIMP_RULE sset
                  [finite_mapTheory.FAPPLY_FUPDATE_THM,
                   pred_setTheory.INSERT_UNION_EQ,
                   pred_setTheory.UNION_EMPTY])
  val ths = TypeBase.constructors_of ``:MMLnonT`` |> map mkrule
in
    save_thm("cmlG_applied", LIST_CONJ ths)
end

val cmlG_FDOM = save_thm("cmlG_FDOM",
  SIMP_CONV (srw_ss()) [cmlG_def] ``FDOM cmlG.rules``)

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
         nullableML_def, c1, condc, cmlG_FDOM, cmlG_applied]);

val safenml = LIST_CONJ (List.take(CONJUNCTS nullableML_def, 2))

val nullML_t = prim_mk_const {Thy = "NTproperties", Name = "nullableML"}

val nullloop_th = prove(
  ``nullableML G (N INSERT sn) (NT N :: rest) = F``,
  simp[Once nullableML_def]);

val null2 = prove(
  ``nullableML G sn (x :: y :: z) <=>
      nullableML G sn [x] ∧ nullableML G sn [y] ∧
      nullableML G sn z``,
  simp[Once nullableML_by_singletons, SimpLHS] >>
  dsimp[] >> simp[GSYM nullableML_by_singletons]);


fun prove_nullable domapp sn acc G_t t = let
  val gML_t = ``nullableML ^G_t sn [NT ^t]``
  open combinTheory pairTheory
  val gML1_th =
      (REWR_CONV (last (CONJUNCTS nullableML_def)) THENC
       SIMP_CONV (srw_ss())
       (acc @ [domapp, GSPEC_INTER, nullloop_th,
               RIGHT_INTER_OVER_UNION, o_ABS_R, S_ABS_R, S_ABS_L,
               GSPEC_applied, o_UNCURRY_R, S_UNCURRY_R, INSERT_INTER, safenml,
               null2]) THENC
       SIMP_CONV (bool_ss ++ boolSimps.COND_elim_ss)
                 [NOT_INSERT_EMPTY]) gML_t
  fun mend th0 =
      if not (is_eq (concl th0)) then
        EQF_INTRO th0
        handle HOL_ERR _ => EQT_INTRO th0
                            handle HOL_ERR _ => th0
      else th0
in
  if is_const (rhs (concl gML1_th)) then gML1_th :: acc
  else
    let
      fun findp t = let
        val (f,args) = strip_comb t
      in
        same_const nullML_t f andalso length args = 3
      end
      val nml_ts = find_terms findp (rhs (concl gML1_th))
      val ts = List.foldl
                 (fn (t, acc) => HOLset.add(acc, rand (lhand (rand t))))
                 empty_tmset nml_ts
      fun foldthis (t', a) =
          if HOLset.member(sn, t') then a
          else prove_nullable domapp (HOLset.add(sn,t)) a G_t t'
      val acc = HOLset.foldl foldthis acc ts
      val th0 = mend (SIMP_RULE bool_ss acc gML1_th)
    in
      if can (find_term findp) (rhs (concl th0)) then
        let
          val th' = CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [th0])) th0
        in
          mend (REWRITE_RULE [IN_INSERT] th') :: acc
        end
      else
        th0 :: acc
    end
end

local val domapp = CONJ cmlG_applied cmlG_FDOM
in
fun fold_nullprove (t, a) =
    prove_nullable domapp empty_tmset a ``cmlG`` ``mkNT ^t``
end

val nullacc =
    foldl fold_nullprove [] [``nE``, ``nType``, ``nTyvarN``, ``nSpecLine``,
                             ``nVlist1``, ``nPtuple``, ``nPbase``, ``nLetDec``,
                             ``nTyVarList``, ``nDtypeDecl``, ``nDecl``, ``nE'``,
                             ``nElist1``, ``nCompOps``, ``nListOps``,
                             ``nPapp``, ``nPattern``, ``nRelOps``, ``nMultOps``,
                             ``nAddOps``, ``nDconstructor``, ``nFDecl``, ``nPatternList``,
                             ``nEseq``, ``nEtuple``, ``nTopLevelDecs``, ``nTopLevelDec``]

local
  fun appthis th = let
    val th' = th |> Q.INST [`sn` |-> `{}`]
                 |> REWRITE_RULE [GSYM nullableML_EQN, NOT_IN_EMPTY]
    fun trydn t = dest_neg t handle HOL_ERR _ => t
    val t = th' |> concl |> trydn |> rand |> lhand |> rand |> rand
    val nm = "nullable_" ^ String.extract(term_to_string t, 1, NONE)
  in
    save_thm(nm, th'); export_rewrites [nm]
  end
in
val _ = List.app appthis nullacc
end

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

val fringe_length_not_nullable = store_thm(
  "fringe_length_not_nullable",
  ``∀G s. ¬nullable G [s] ⇒
          ∀pt. ptree_head pt = s ⇒ valid_ptree G pt ⇒
               0 < LENGTH (ptree_fringe pt)``,
  spose_not_then strip_assume_tac >>
  `LENGTH (ptree_fringe pt) = 0` by decide_tac >>
  fs[listTheory.LENGTH_NIL] >>
  erule mp_tac grammarTheory.valid_ptree_derive >>
  fs[NTpropertiesTheory.nullable_def]);

val derives_singleTOK = store_thm(
  "derives_singleTOK",
  ``derives G [TOK t] l ⇔ (l = [TOK t])``,
  simp[Once relationTheory.RTC_CASES1, grammarTheory.derive_def] >>
  metis_tac[]);
val _ = export_rewrites ["derives_singleTOK"]

val fringe_lengths_V = store_thm(
  "fringe_lengths_V",
  ``fringe_lengths cmlG [NT (mkNT nV)] = {1}``,
  simp[fringe_lengths_def] >>
  simp[Once relationTheory.RTC_CASES1, MAP_EQ_SING, cmlG_FDOM] >>
  dsimp[MAP_EQ_SING,cmlG_applied] >>
  simp[EXTENSION, EQ_IMP_THM] >> qx_gen_tac `t` >> rpt strip_tac >>
  fs[] >> qexists_tac `[AlphaT "foo"]` >>
  simp[stringTheory.isUpper_def]);

val parsing_ind = save_thm(
  "parsing_ind",
  relationTheory.WF_INDUCTION_THM
    |> Q.ISPEC `inv_image
                  (measure (LENGTH:(token,MMLnonT)symbol list -> num) LEX
                   measure (λn. case n of TOK _ => 0 | NT n => NT_rank n))
                  (λpt. (ptree_fringe pt, ptree_head pt))`
    |> SIMP_RULE (srw_ss()) [pairTheory.WF_LEX, relationTheory.WF_inv_image]
    |> SIMP_RULE (srw_ss()) [relationTheory.inv_image_def,
                             pairTheory.LEX_DEF]);


(*
val cmlvalid_not_INR = store_thm(
  "cmlvalid_not_INR",
  ``cmlvalid pt ∧ ptree_fringe pt = MAP TOK i ⇒ ptree_head pt ≠ NT (INR n)``,
  Cases_on `pt` >>
  dsimp[MAP_EQ_SING, cmlvalid_thm] >> rpt strip_tac >> rw[] >>
  fs[cml_okrule_eval_th])

val mkelim_tac =
  gen_tac >> Cases_on `pt` >> simp[cmlvalid_def] >> rw[] >>
  fs[cmlG_FDOM,cmlG_applied] >> Cases_on `l` >> fs[] >>
  Cases_on `h` >> fs[]
fun mkelim_th t = prove(
  ``∀pt. ptree_head pt = NN ^t ⇒ cmlvalid pt ⇒
         pt = Lf (NN ^t) ∨ ∃t. pt = Nd (mkNT ^t) [Lf (TOK t)]``,
  mkelim_tac)

val elimV_thm = mkelim_th ``nV``
val elimUQTyop_thm = mkelim_th ``nUQTyOp``
fun elim_tac th q = let
  fun c1 eqth = let
    val th' = MATCH_MP th eqth handle HOL_ERR _ => MATCH_MP th (SYM eqth)
  in
    first_assum (fn cmlvth => mp_tac (MATCH_MP th' cmlvth))
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
    qispl_then [`cmlG`] mp_tac fringe_length_ptree >>
    disch_then (qspecl_then [`[]`, `vlt`] mp_tac) >>
    simp[SYM nullable_fringe_lengths, cmlvalid_SYM] >>
    metis_tac [nullable_Vlist1]

val cmlGNIL =
    fringe_length_ptree
      |> ISPEC ``cmlG`` |> Q.SPEC `[]`
      |> SIMP_RULE (srw_ss()) [SYM nullable_fringe_lengths,
                               GSYM AND_IMP_INTRO, cmlvalid_SYM]

val head_TOK = prove(
  ``∀pt t. ptree_head pt = TOK t ⇒ cmlvalid pt ⇒ pt = Lf (TOK t)``,
  Cases >> simp[]);

val elimTyOp_thm = prove(
  ``∀pt. ptree_head pt = NN nTyOp ⇒ cmlvalid pt ⇒
         LENGTH (ptree_fringe pt) = 1``,
  gen_tac >> Cases_on `pt` >> simp[cmlvalid_def] >> rw[] >>
  fs[MAP_EQ_SING,cmlG_FDOM,cmlG_applied] >> rveq >> fs[]
  >- (fs[cmlvalid_SYM] >> elim_tac elimUQTyop_thm `t`) >>
  fs[cmlvalid_SYM] >> erule SUBST_ALL_TAC head_TOK >> simp[]);

val balance_def = Define`
  balance stk l r [] = SOME stk ∧
  balance stk l r (c::cs) =
    if c = l then balance (l::stk) l r cs
    else if c = r then
      if stk ≠ [] ∧ HD stk = l then balance (TL stk) l r cs
      else NONE
    else balance stk l r cs
`
val _ = export_rewrites ["balance_def"]

val balance_APPEND = store_thm(
  "balance_APPEND",
  ``∀stk.
      balance stk l r (s1 ++ s2) =
      case balance stk l r s1 of
          NONE => NONE
        | SOME stk' => balance stk' l r s2``,
  Induct_on `s1` >> rw[])
val _ = overload_on("balanced", ``λstk l r s. balance stk l r s = SOME []``)

val balanced_APPEND = store_thm(
  "balanced_APPEND",
  ``∀stk. balanced stk l r s1 ∧ balanced [] l r s2 ⇒
          balanced stk l r (s1 ++ s2)``,
  simp[balance_APPEND]);

val balance_APPEND_stack = store_thm(
  "balance_APPEND_stack",
  ``∀s stk stk' stk2.
       (balance stk l r s = SOME stk') ⇒
       (balance (stk ++ stk2) l r s = SOME (stk' ++ stk2))``,
  Induct_on `s` >> simp[] >> qx_gen_tac `h` >> Cases_on `h = l` >> simp[]
  >- metis_tac [listTheory.APPEND] >>
  Cases_on `h = r` >> simp[] >> qx_gen_tac `stk` >>
  `stk = [] ∨ ∃h2 t. stk = h2 :: t` by (Cases_on `stk` >> simp[]) >> simp[] >>
  Cases_on `h2 = l` >> simp[]);

val balanced_APPEND_safe1 = store_thm(
  "balanced_APPEND_safe1",
  ``∀stk. balanced [] l r s1 ⇒
          (balanced stk l r (s1 ++ s2) ⇔ balanced stk l r s2)``,
  simp[balance_APPEND] >> gen_tac >>
  qispl_then [`s1`, `[]`, `[]`] mp_tac balance_APPEND_stack >> simp[]);


val protected_by_def = Define`
  protected_by t gds s =
    ∀i. i < LENGTH s ∧ EL i s = t ⇒
        ∃gli gri. gli < i ∧ i < gri ∧ gri < LENGTH s ∧
                  (EL gli s,EL gri s) ∈ gds ∧
                  balanced [] (EL gli s) (EL gri s)
                           (TAKE (gri - gli - 1) (DROP (gli + 1) s))
`

val protected_by_APPEND = store_thm(
  "protected_by_APPEND",
  ``protected_by t gds s1 ∧ protected_by t gds s2 ⇒
    protected_by t gds (s1 ++ s2)``,
  simp[protected_by_def] >> rw[] >>
  Cases_on `i < LENGTH s1`
  >- (first_x_assum (fn th => qspec_then `i` mp_tac th >>
                              CHANGED_TAC (ASM_REWRITE_TAC [])) >>
      first_x_assum (qspec_then `i` (K ALL_TAC)) >>
      simp[rich_listTheory.EL_APPEND1] >>
      disch_then (qxchl [`gli`, `gri`] strip_assume_tac) >>
      map_every qexists_tac [`gli`, `gri`] >>
      asimp[rich_listTheory.EL_APPEND1, rich_listTheory.DROP_APPEND1,
            rich_listTheory.TAKE_APPEND1]) >>
  fs[DECIDE ``¬(x:num < y) ⇔ y ≤ x``] >>
  first_x_assum
    (fn th => qspec_then `i - LENGTH s1` mp_tac th >>
              CHANGED_TAC (asimp[rich_listTheory.EL_APPEND2])) >>
  first_x_assum (qspec_then `i` (K ALL_TAC)) >>
  disch_then (qxchl [`gli`, `gri`] strip_assume_tac) >>
  map_every qexists_tac [`gli + LENGTH s1`, `gri + LENGTH s1`] >>
  asimp[rich_listTheory.EL_APPEND2, rich_listTheory.TAKE_APPEND2,
        rich_listTheory.DROP_APPEND2]);

val protected_by_SING = store_thm(
  "protected_by_SING",
  ``protected_by t1 gds [t2] ⇔ t1 ≠ t2``,
  simp[protected_by_def, DECIDE ``i < 1n ⇔ i = 0``] >> metis_tac[]);
val _ = export_rewrites ["protected_by_SING"]

val protected_by_NIL = store_thm(
  "protected_by_NIL",
  ``protected_by t gds [] = T``,
  simp[protected_by_def]);
val _ = export_rewrites ["protected_by_NIL"]

val protects_def = Define`
  protects N toks guards =
    ∀pt. cmlvalid pt ∧ ptree_head pt = NN N ⇒
         (∀t. t ∈ toks ⇒ protected_by t guards (ptree_fringe pt)) ∧
         (∀gl gr. (gl,gr) ∈ guards ⇒ balanced [] gl gr (ptree_fringe pt))
`

fun loseC c =
    first_x_assum
      (K ALL_TAC o assert (can (find_term (same_const c)) o concl))

val lose_rank = loseC ``NT_rank``

val cmlvalid_Lf = store_thm(
  "cmlvalid_Lf",
  ``cmlvalid (Lf s)``,
  simp[cmlvalid_def])
val _ = export_rewrites ["cmlvalid_Lf"]


val ptree_head_t = ``ptree_head``
val NT_rank_t = ``NT_rank``
fun single_rank_tac (asl,g) = let
  fun filter_this t =
    is_eq t andalso same_const ptree_head_t (rator (lhs t))
in
  case filter filter_this asl of
      [t] =>
      let
        val pt_t = rand (lhs t)
      in
        first_x_assum (mp_tac o SPEC pt_t o
                       assert (can (find_term (same_const NT_rank_t)) o
                               concl)) >>
        simp[NT_rank_def]
      end
    | _ => NO_TAC
end (asl,g)

(*
val allpar_balanced = store_thm(
  "allpar_balanced",
  ``∀pt N. ptree_head pt = NN N ⇒ cmlvalid pt ⇒
           balanced [] (TK LparT) (TK RparT) (ptree_fringe pt)``,
  ho_match_mp_tac parsing_ind >> qx_gen_tac `pt` >> strip_tac >>
  qx_gen_tac `N` >> fs[cmlvalid_def] >>
  rpt strip_tac >>
  `(∃s. pt = Lf s) ∨ (∃N' subs. pt = Nd N' subs)` by (Cases_on `pt` >> simp[])>>
  fs[] >> rveq >>
  Cases_on `N` >> fs[cmlG_FDOM,MAP_EQ_CONS,cmlG_applied] >> rveq >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  TRY single_rank_tac >>
  TRY (fs[cmlvalid_SYM] >>
       rpt (erule SUBST_ALL_TAC head_TOK >> fs[]) >>
       asimp[balanced_APPEND, balanced_APPEND_safe1] >> NO_TAC)
  >- (lose_rank >> erule assume_tac V_fringe_length >>
      erule assume_tac Vlist1_fringe_length >> asimp[balanced_APPEND])
  >- (erule assume_tac TopLevelDec_fringe_length >>
      match_mp_tac balanced_APPEND >> conj_tac
      >- (asm_match `ptree_head tlpt = NN nTopLevelDec` >>
          asm_match `ptree_head tlspt = NN nTopLevelDecs` >>
          Cases_on `ptree_fringe tlspt`
          >- first_x_assum (fn th => qspec_then `tlpt` mp_tac th >>
                                     simp[NT_rank_def]) >>
          asimp[]) >>
      asimp[])
  >- (fs[cmlvalid_SYM] >> rpt (erule SUBST_ALL_TAC head_TOK >> fs[]) >>
      lose_rank >> rw[] >> rpt (match_mp_tac balanced_APPEND >> conj_tac) >>
      asimp[])
  >- (erule assume_tac SpecLine_fringe_length >>
      match_mp_tac balanced_APPEND >> conj_tac
      >- (asm_match `ptree_head sllpt = NN nSpecLineList` >>
          Cases_on `ptree_fringe sllpt`
          >- (asm_match `ptree_head slpt = NN nSpecLine` >>
              first_x_assum (fn th => qspec_then `slpt` mp_tac th >>
                                      simp[NT_rank_def]>> NO_TAC)) >>
          asimp[]) >>
      asimp[])
  >- (erule assume_tac ConstructorName_fringe_length >>
      erule assume_tac Ptuple_fringe_length >>
      asimp[balanced_APPEND])
  >- (erule assume_tac ConstructorName_fringe_length >>
      erule assume_tac Pbase_fringe_length >> asimp[balanced_APPEND])
  >- (erule assume_tac LetDec_fringe_length >>
      match_mp_tac balanced_APPEND >> conj_tac
      >- (asm_match `ptree_head lds = NN nLetDecs` >>
          Cases_on `ptree_fringe lds`
          >- (asm_match `ptree_head ld = NN nLetDec` >>
              first_x_assum (fn th => qspec_then `ld` mp_tac th >>
                                      simp[NT_rank_def])) >>
          asimp[]) >>
      asimp[])
  >-
)))




res_tac) >>
  >- (fs[cmlvalid_SYM] >> erule SUBST_ALL_TAC head_TOK >> simp[]) >>
  >- (fs[cmlvalid_SYM] >> erule SUBST_ALL_TAC head_TOK >> simp[]) >>






fun mkpar_balanced_t t =
  ``∀pt. ptree_head pt = NN ^t ⇒ cmlvalid pt ⇒
         balanced [] (TK LparT) (TK RparT) (ptree_fringe pt)``


val Type_protects_comma = store_thm(
  "Type_protects_comma",
  ``(∀n. n ∈ {nType; nDType; nTyOp} ⇒
         protects n {TOK CommaT} {(TOK LparT, TOK RparT)}) ∧
    (∀pt. cmlvalid pt ∧ ptree_head pt = NN nTypeList ⇒
          balanced [] (TK LparT) (TK RparT) (ptree_fringe pt))``,
  simp[protects_def, GSYM RIGHT_FORALL_IMP_THM] >>
  CONV_TAC (LAND_CONV SWAP_VARS_CONV) >>
  simp[GSYM FORALL_AND_THM] >>
  Q.ISPEC_THEN
    `inv_image
        (measure (LENGTH:(token,MMLnonT)symbol list -> num) LEX
         measure (λn. case n of TOK _ => 0 | NT n => NT_rank n))
        (λpt. (ptree_fringe pt, ptree_head pt))`
    (HO_MATCH_MP_TAC o
     SIMP_RULE (srw_ss()) [pairTheory.WF_LEX, relationTheory.WF_inv_image])
    relationTheory.WF_INDUCTION_THM >>
  simp[relationTheory.inv_image_def, pairTheory.LEX_DEF] >>
  qx_gen_tac `pt` >> strip_tac >>
  Cases_on `pt`
  >- simp[DECIDE ``i < 1n ⇔ i = 0``] >>
  conj_tac >| [ntac 3 strip_tac, ALL_TAC] >>
  rveq >> fs[cmlvalid_def] >> rveq >>
  fs(MAP_EQ_CONS::cmlG_FDOM::cmlG_applied) >> rveq >> fs[]
  >- simp[NT_rank_def]
  >- (fs[DISJ_IMP_THM, FORALL_AND_THM, cmlvalid_SYM] >>
      erule SUBST_ALL_TAC head_TOK >> fs[] >> rw[] >> lose_rank
      >- simp[protected_by_APPEND] >>
      simp[balanced_APPEND])
  >- (fs[cmlvalid_SYM] >> erule SUBST_ALL_TAC head_TOK >> simp[])
  >- simp[NT_rank_def]
  >- (fs[DISJ_IMP_THM, FORALL_AND_THM, AND_IMP_INTRO, IMP_CONJ_THM] >>
      rpt lose_rank >> rpt (loseC ``nType``) >>
      erule assume_tac DType_fringe_length >>
      fs[cmlvalid_SYM] >> erule assume_tac elimTyOp_thm >> fs[] >>
      asimp[protected_by_APPEND, balanced_APPEND])
  >- (fs[DISJ_IMP_THM, FORALL_AND_THM, AND_IMP_INTRO, IMP_CONJ_THM] >>
      rpt lose_rank >> rpt (loseC ``nType``) >> rpt (loseC ``nDType``) >>
      fs[cmlvalid_SYM] >>
      rpt (erule SUBST_ALL_TAC head_TOK >> fs[]) >>
      asm_match `ptree_head tlpt = NN nTypeList` >>
      `balanced [] (TK LparT) (TK RparT) (ptree_fringe tlpt)` by asimp[] >>
      conj_tac
      >- (REWRITE_TAC [listTheory.APPEND |> GSYM |> CONJUNCT2] >>
          match_mp_tac protected_by_APPEND >> asimp[] >>
          simp[protected_by_def] >> qx_gen_tac `i` >> rpt strip_tac >>
          map_every qexists_tac [`0`, `SUC (LENGTH (ptree_fringe tlpt))`] >>
          asimp[rich_listTheory.TAKE_APPEND2, rich_listTheory.EL_APPEND2] >>
          `i ≠ 0` by (strip_tac >> fs[]) >> asimp[] >>
          spose_not_then strip_assume_tac >>
          `i = SUC (LENGTH (ptree_fringe tlpt))` by decide_tac >> rveq >>
          fs[rich_listTheory.EL_APPEND2]) >>
      match_mp_tac balanced_APPEND >> asimp[] >>
      simp[balanced_APPEND_safe1])
  >- (fs[DISJ_IMP_THM, FORALL_AND_THM, AND_IMP_INTRO, IMP_CONJ_THM] >>
      rpt lose_rank >> rpt (loseC ``nTyOp``) >> rpt (loseC ``nDType``) >>
      fs[cmlvalid_SYM] >>
      rpt (erule SUBST_ALL_TAC head_TOK >> fs[]) >>
      asm_match `ptree_head typt = NN nType` >>
      `protected_by (TK CommaT) {(TK LparT, TK RparT)} (ptree_fringe typt)`
        by asimp[] >> REWRITE_TAC [listTheory.APPEND |> GSYM |> CONJUNCT2] >>
      conj_tac
      >- (match_mp_tac protected_by_APPEND >> simp[] >>
          `TK LparT :: ptree_fringe typt = [TK LparT] ++ ptree_fringe typt`
            by simp[] >>
          pop_assum SUBST_ALL_TAC >>
          match_mp_tac protected_by_APPEND >> simp[]) >>
      asimp[balanced_APPEND_safe1])
  >- (fs[cmlvalid_SYM] >> elim_tac elimUQTyop_thm `t` >>
      fs(cmlvalid_def::cmlG_FDOM::cmlG_applied))
  >- (fs[cmlvalid_SYM] >> erule SUBST_ALL_TAC head_TOK >> simp[]) >>
  strip_tac >> rveq >> fs[] >>
  fs (MAP_EQ_CONS::cmlG_applied) >> rveq >> fs[]
  >- simp[NT_rank_def] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM, AND_IMP_INTRO, IMP_CONJ_THM] >>
  rpt lose_rank >> rpt (loseC ``nTyOp``) >> rpt (loseC ``nDType``) >>
  fs[cmlvalid_SYM] >> erule SUBST_ALL_TAC head_TOK >> fs[] >>
  asimp[balanced_APPEND])

val unambiguous = store_thm(
  "unambiguous",
  ``∀i N p1 p2.
      valid_ptree cmlG p1 ∧ ptree_fringe p1 = MAP TOK i ∧
      ptree_head p1 = NT N ∧
      valid_ptree cmlG p2 ∧ ptree_fringe p2 = MAP TOK i ∧
      ptree_head p2 = NT N ⇒
      p1 = p2``,
  ntac 2 gen_tac >> `∃iN. iN = (i,N)` by simp[] >> pop_assum mp_tac >>
  map_every qid_spec_tac [`N`, `i`, `iN`] >>
  Q.ISPEC_THEN
    `measure (LENGTH:token list -> num) LEX measure (NT_rank: NT -> num)`
    (HO_MATCH_MP_TAC o SIMP_RULE (srw_ss()) [pairTheory.WF_LEX])
    relationTheory.WF_INDUCTION_THM >>
  dsimp[pairTheory.LEX_DEF, AND_IMP_INTRO, cmlvalid_SYM] >>
  rpt strip_tac >>
  `(∃x. N = INR x) ∨ ∃n. N = INL n` by (Cases_on `N` >> simp[])
  >- metis_tac[cmlvalid_not_INR] >> rw[] >>
  Cases_on `n`
  >- ((* nVlist1 *) Cases_on `p1` >> fs[MAP_EQ_SING] >> rw[] >>
      Cases_on `p2` >>
      fs[MAP_EQ_SING, cmlvalid_thm, cml_okrule_eval_th, MAP_EQ_CONS] >>
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
      fs[MAP_EQ_SING,cmlvalid_def,cmlG_FDOM,cmlG_applied] >>
      rveq >> fs[cmlvalid_SYM, MAP_EQ_CONS] >> rveq >>
      fs[DISJ_IMP_THM, FORALL_AND_THM]
      >- (elim_tac elimUQTyop_thm `t1` >> elim_tac elimUQTyop_thm `t2`)
      >- (elim_tac elimUQTyop_thm `t1` >>
          elim_tac elimUQTyop_thm `t2` >> fs[] >>
          imp_res_tac cmlGNIL >> ntac 3 (pop_assum mp_tac) >>
          simp[])
      >- (elim_tac elimUQTyop_thm `t1` >>
          fs[grammarTheory.MAP_EQ_APPEND, MAP_EQ_SING] >>
          elim_tac elimUQTyop_thm `t2` >> fs[] >>
          imp_res_tac cmlGNIL >> pop_assum mp_tac >> simp[])
      >- (elim_tac elimUQTyop_thm `t1` >>
          imp_res_tac cmlGNIL >> ntac 3 (pop_assum mp_tac) >> simp[])
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
          elim_tac elimUQTyop_thm `t` >> erule mp_tac cmlGNIL >>
          simp[nullable_UQTyOp])
      >- (rpt
            (erule SUBST_ALL_TAC head_TOK >> fs[MAP_EQ_SING]) >>
          pop_assum (assume_tac o SYM) >> fs[]) >>
      rpt (erule SUBST_ALL_TAC head_TOK >> fs[MAP_EQ_SING]) >>
      pop_assum (assume_tac o SYM) >> fs[] >>
      elim_tac elimUQTyop_thm `t1` >> fs[MAP_EQ_CONS])
  >- ((* nTypeList *)
      Cases_on `p1` >> fs[MAP_EQ_SING] >> rveq >>
      Cases_on `p2` >> fs[MAP_EQ_SING] >> rveq >>
      fs[cmlvalid_thm, cml_okrule_eval_th, MAP_EQ_CONS] >> rveq >>
      fs[]
      >- (rank_assum >> simp[NT_rank_def])
      >- (erule SUBST_ALL_TAC head_TOK)


*)

*)
val _ = export_theory()
