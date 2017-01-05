open preamble
open mp_then

open simple_grammarTheory gramTheory
open NTpropertiesTheory

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

val APPEND_EQ_SING' = CONV_RULE (LAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))
                                listTheory.APPEND_EQ_SING
val _ = augment_srw_ss [rewrites [APPEND_EQ_SING']]

val _ = new_theory "gramProps"
val _ = set_grammar_ancestry ["gram", "NTproperties", "simple_grammar"]

val NT_rank_def = Define`
  NT_rank N =
    case N of
      | INR _ => 0n
      | INL n =>
        if n = nElist1                 then 16
        else if n = nEseq              then 16
        else if n = nTopLevelDecs      then 16
(*      else if n = nREPLTop           then 16 *)
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
        else if n = nNonETopLevelDecs  then  4
        else if n = nTopLevelDec       then  3
        else if n = nDecls             then  3
        else if n = nStructure         then  2
        else if n = nDecl              then  2
        else if n = nTypeDec           then  1
        else if n = nSpecLineList      then  3
        else if n = nSpecLine          then  2
        else if n = nPtuple            then  2
        else if n = nPbase             then  3
        else if n = nPbaseList1        then  4
        else if n = nPapp              then  4
        else if n = nPcons             then  5
        else if n = nPattern           then  6
        else if n = nPatternList       then  7
        else if n = nPEs               then  8
        else if n = nPE                then  7
        else if n = nPE'               then  7
        else if n = nLetDecs           then  2
        else if n = nLetDec            then  1
        else if n = nDtypeDecl         then  3
        else if n = nAndFDecls         then  3
        else if n = nFDecl             then  2
        else if n = nTyVarList         then  2
        else if n = nTyvarN            then  1
        else                                 0
`

fun ty2frag ty = let
  open simpLib
  val {convs,rewrs} = TypeBase.simpls_of ty
in
  merge_ss (rewrites rewrs :: map conv_ss convs)
end
val GRAM_ss = ty2frag ``:(α,β)grammar``

fun grammar_applied gnm G_def rules_t nt_ty = let
  val rules = SIMP_CONV (bool_ss ++ GRAM_ss)
                      [G_def, combinTheory.K_DEF,
                       finite_mapTheory.FUPDATE_LIST_THM] rules_t
  val app0 = finite_mapSyntax.fapply_t
  val theta =
      Type.match_type (type_of app0 |> dom_rng |> #1) (type_of rules_t)
  val app = inst theta app0
  val app_rules = AP_TERM app rules
  val sset = bool_ss ++ ty2frag ``:'a + 'b`` ++ ty2frag nt_ty
  fun mkrule t =
      (print (gnm ^ "_applied: " ^ term_to_string t ^"\n");
       AP_THM app_rules ``INL ^t : ^(ty_antiq nt_ty) inf``
              |> SIMP_RULE sset
                  [finite_mapTheory.FAPPLY_FUPDATE_THM,
                   pred_setTheory.INSERT_UNION_EQ,
                   pred_setTheory.UNION_EMPTY])
  val ths = TypeBase.constructors_of nt_ty |> map mkrule
in
    save_thm(gnm ^ "_applied", LIST_CONJ ths)
end

val cmlG_applied = grammar_applied "cmlG" cmlG_def ``cmlG.rules`` ``:MMLnonT``
val scmlG_applied =
    grammar_applied "scmlG" scmlG_def ``scmlG.rules`` ``:SCMLnonT``

val cmlG_FDOM = save_thm("cmlG_FDOM",
  SIMP_CONV (srw_ss()) [cmlG_def] ``FDOM cmlG.rules``)

val scmlG_FDOM = save_thm("scmlG_FDOM",
  SIMP_CONV (srw_ss()) [scmlG_def] ``FDOM scmlG.rules``)

val paireq = Q.prove(
  `(x,y) = z ⇔ x = FST z ∧ y = SND z`, Cases_on `z` >> simp[])

val GSPEC_INTER = Q.prove(
  `GSPEC f ∩ Q =
    GSPEC (S ($, o FST o f) (S ($/\ o SND o f) (Q o FST o f)))`,
  simp[GSPECIFICATION, EXTENSION, SPECIFICATION] >> qx_gen_tac `e` >>
  simp[paireq] >> metis_tac[])

val RIGHT_INTER_OVER_UNION = Q.prove(
  `(a ∪ b) ∩ c = (a ∩ c) ∪ (b ∩ c)`,
  simp[EXTENSION] >> metis_tac[]);

val GSPEC_applied = Q.prove(
  `GSPEC f x ⇔ x IN GSPEC f`,
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

val nullloop_th = Q.prove(
  `nullableML G (N INSERT sn) (NT N :: rest) = F`,
  simp[Once nullableML_def]);

val null2 = Q.prove(
  `nullableML G sn (x :: y :: z) <=>
      nullableML G sn [x] ∧ nullableML G sn [y] ∧
      nullableML G sn z`,
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
    foldl fold_nullprove []
          [“nE”, “nType”, “nTyvarN”, “nSpecLine”,
           “nPtuple”, “nPbase”, “nLetDec”,
           “nTyVarList”, “nDtypeDecl”, “nDecl”, “nE'”,
           “nElist1”, “nCompOps”, “nListOps”,
           “nPapp”, “nPattern”, “nRelOps”, “nMultOps”,
           “nAddOps”, “nDconstructor”, “nFDecl”,
           “nPatternList”, “nPbaseList1”, “nElist2”,
           “nEseq”, “nEtuple”, “nTopLevelDecs”, “nTopLevelDec”]

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
val fringe_length_ptree = Q.store_thm(
  "fringe_length_ptree",
  `∀G i pt. ptree_fringe pt = MAP TOK i ∧ valid_ptree G pt ⇒
           LENGTH i ∈ fringe_lengths G [ptree_head pt]`,
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

val fringe_length_not_nullable = Q.store_thm(
  "fringe_length_not_nullable",
  `∀G s. ¬nullable G [s] ⇒
          ∀pt. ptree_head pt = s ⇒ valid_ptree G pt ⇒
               0 < LENGTH (ptree_fringe pt)`,
  spose_not_then strip_assume_tac >>
  `LENGTH (ptree_fringe pt) = 0` by decide_tac >>
  fs[listTheory.LENGTH_NIL] >>
  erule mp_tac grammarTheory.valid_ptree_derive >>
  fs[NTpropertiesTheory.nullable_def]);

val derives_singleTOK = Q.store_thm(
  "derives_singleTOK",
  `derives G [TOK t] l ⇔ (l = [TOK t])`,
  simp[Once relationTheory.RTC_CASES1, grammarTheory.derive_def] >>
  metis_tac[]);
val _ = export_rewrites ["derives_singleTOK"]

val fringe_lengths_V = Q.store_thm(
  "fringe_lengths_V",
  `fringe_lengths cmlG [NT (mkNT nV)] = {1}`,
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
                  (measure (LENGTH:(token,MMLnonT)grammar$symbol list -> num)
                     LEX
                   measure (λn. case n of TOK _ => 0 | NT n => NT_rank n))
                  (λpt. (ptree_fringe pt, ptree_head pt))`
    |> SIMP_RULE (srw_ss()) [pairTheory.WF_LEX, relationTheory.WF_inv_image]
    |> SIMP_RULE (srw_ss()) [relationTheory.inv_image_def,
                             pairTheory.LEX_DEF]);

val gen_valid_ptree_ind = Q.store_thm(
  "gen_valid_ptree_ind",
  ‘∀G P.
     (∀t. P (Lf t)) ∧
     (∀N children.
       (∀cpt. MEM cpt children ⇒ P cpt) ∧
       (∀cpt. MEM cpt children ⇒ valid_ptree G cpt) ∧
       N ∈ FDOM G.rules ∧ MAP ptree_head children ∈ G.rules ' N ⇒
       P (Nd N children)) ⇒
     ∀pt. valid_ptree G pt ⇒ P pt’,
  rpt gen_tac >> strip_tac >>
  `(∀pt. valid_ptree G pt ⇒ P pt) ∧
   (∀ptl. EVERY (valid_ptree G) ptl ⇒ EVERY P ptl)` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of “:(α,β) parsetree”) >>
  simp[grammarTheory.valid_ptree_def, EVERY_MEM]);

val correspondingNT_def = Define `
  correspondingNT nAddOps = SOME snAddOps ∧
  correspondingNT nDtypeDecls = SOME snDtypeDecls ∧
  correspondingNT nE = SOME snExpr ∧
  correspondingNT nTyOp = SOME snTyOp ∧
  correspondingNT nTypeAbbrevDec = SOME snTypeAbbrevDec ∧
  correspondingNT nTypeDec = SOME snTypeDec ∧
  correspondingNT nTypeList1 = SOME snTypeList1 ∧
  correspondingNT nTypeList2 = SOME snTypeList2 ∧
  correspondingNT nTypeName = SOME snTypeName ∧
  correspondingNT nTyvarN = SOME snTyvarN ∧
  correspondingNT nTyVarList = SOME snTyVarList ∧
  correspondingNT nUQConstructorName = SOME snUQConstructorName ∧
  correspondingNT nUQTyOp = SOME snUQTyOp ∧
  correspondingNT nV = SOME snV ∧
  correspondingNT nType = SOME snType ∧
  correspondingNT nTbase = SOME snType ∧
  correspondingNT nDType = SOME snType ∧
  correspondingNT nPType = SOME snType ∧
  correspondingNT _ = NONE
`
val _ = export_rewrites ["correspondingNT_def"]

val corresponding_EQ0 = Q.prove(
  ‘(correspondingNT n = SOME snV ⇔ n = nV) ∧
   (correspondingNT n = SOME snTypeAbbrevDec ⇔ n = nTypeAbbrevDec) ∧
   (correspondingNT n = SOME snDtypeDecls ⇔ n = nDtypeDecls) ∧
   (correspondingNT n = SOME snTypeDec ⇔ n = nTypeDec) ∧
   (correspondingNT n = SOME snTyOp ⇔ n = nTyOp) ∧
   (correspondingNT n = SOME snUQTyOp ⇔ n = nUQTyOp) ∧
   (correspondingNT n = SOME snUQConstructorName ⇔ n = nUQConstructorName) ∧
   (correspondingNT n = SOME snTypeList1 ⇔ n = nTypeList1) ∧
   (correspondingNT n = SOME snTypeList2 ⇔ n = nTypeList2) ∧
   (correspondingNT n = SOME snTypeName ⇔ n = nTypeName) ∧
   (correspondingNT n = SOME snTyVarList ⇔ n = nTyVarList) ∧
   (correspondingNT n = SOME snTyvarN ⇔ n = nTyvarN)’,
  Cases_on `n` >> simp[])

val corresponding_EQ = save_thm(
  "corresponding_EQ[simp]",
  LIST_CONJ (map (fn th => CONJ th (CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ))
                                              th))
                 (CONJUNCTS corresponding_EQ0)))

val ptree_head_EQ_TOK = Q.store_thm(
  "ptree_head_EQ_TOK[simp]",
  ‘((ptree_head pt = TOK t) ⇔ (pt = Lf (TOK t))) ∧
   ((TOK t = ptree_head pt) ⇔ (pt = Lf (TOK t)))’,
  Cases_on `pt` >> simp[] >> metis_tac[])

val ptree_head_EQ_NT = Q.prove(
  ‘ptree_head pt = NT n ⇔ (∃cpts. pt = Nd n cpts) ∨ pt = Lf (NT n)’,
  Cases_on ‘pt’ >> simp[]);

fun flipeq_conv t = let
  val (l,r) = dest_eq t
in
  if null (free_vars l) andalso not (null (free_vars r)) then
    REWR_CONV EQ_SYM_EQ t
  else NO_CONV t
end
val FLIPEQ_ss =
  simpLib.SSFRAG { ac = [], congs = [], filter = NONE,
                   name = SOME "FLIPEQ", dprocs = [],
                   rewrs = [],
                   convs = [{conv = K (K flipeq_conv),
                             key = SOME ([], “x:α = y”),
                             name = "flipeq_conv", trace = 2}]}
val _ = augment_srw_ss [FLIPEQ_ss]

val MAP_TOK_11 = Q.store_thm(
  "MAP_TOK_11[simp]",
  ‘MAP TOK s1 = MAP TOK s2 ⇔ s1 = s2’,
  simp[INJ_MAP_EQ_IFF, INJ_DEF]);

val inject_nType = prove(
  “correspondingNT N = SOME snType ∧ ptree_head pt = NN N ∧
   valid_ptree cmlG pt ⇒
   ∃pt'. valid_ptree cmlG pt' ∧ ptree_head pt' = NN nType ∧
         ptree_fringe pt' = ptree_fringe pt”,
  Cases_on ‘N’ >> simp[]
  >- metis_tac[]
  >- (rename1 ‘nTbase’ >> strip_tac >>
      qexists_tac
        ‘Nd (mkNT nType) [Nd (mkNT nPType) [Nd (mkNT nDType) [pt]]]’ >>
      simp[cmlG_applied, cmlG_FDOM])
  >- (rename1 ‘nPType’ >> strip_tac >>
      qexists_tac ‘Nd (mkNT nType) [pt]’ >> simp[cmlG_FDOM, cmlG_applied])
  >- (rename1 ‘nDType’ >> strip_tac >>
      qexists_tac ‘Nd (mkNT nType) [Nd (mkNT nPType) [pt]]’ >>
      simp[cmlG_FDOM, cmlG_applied]))

fun check0 pfx s g = (print (pfx ^ s ^ "\n"); rename1 [QUOTE s] g)

val check = check0 "simple_SUBSET_actual: "

fun nailIHx k =
  first_x_assum
    (REPEAT_GTCL
       (fn ttcl => fn th => first_assum (mp_then (Pos hd) ttcl th))
       (k o assert (not o is_imp o #2 o strip_forall o concl)) o
     assert (is_imp o #2 o strip_forall o concl))

val type_nTyOp_parses_to_nType = Q.store_thm(
  "type_nTyOp_parses_to_nType",
  ‘∀pt1. valid_ptree cmlG pt1 ⇒
         ∀pf1 pt2.
           ptree_fringe pt1 = MAP TK pf1 ∧
           ptree_head pt1 ∈ {NN nType; NN nPType} ∧
           valid_ptree cmlG pt2 ∧ ptree_head pt2 = NN nTyOp ⇒
           ∃pt. valid_ptree cmlG pt ∧ ptree_head pt = ptree_head pt1 ∧
                ptree_fringe pt = ptree_fringe pt1 ++ ptree_fringe pt2’,
  ho_match_mp_tac gen_valid_ptree_ind >> rw[] >>
  fs[cmlG_applied, cmlG_FDOM] >> rveq >>
  fs[MAP_EQ_CONS] >> rveq >>
  fs[MAP_EQ_CONS, DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_APPEND] >> rveq
  >- (nailIHx (Q.X_CHOOSE_THEN ‘pt’ strip_assume_tac) >>
      qexists_tac ‘Nd (mkNT nType) [pt]’ >>
      simp[cmlG_FDOM, cmlG_applied])
  >- (rename [‘ptree_head pt1 = NN nPType’,
              ‘ptree_head pt2 = NN nType’,
              ‘ptree_head pt3 = NN nTyOp’,
              ‘ptree_fringe pt1 = MAP TK pf1’,
              ‘ptree_fringe pt2 = MAP TK pf2’] >> fs[] >>
      ‘∃pt. valid_ptree cmlG pt ∧ ptree_head pt = NN nType ∧
            ptree_fringe pt = MAP TK pf2 ++ ptree_fringe pt3’ by metis_tac[] >>
      qexists_tac ‘Nd (mkNT nType) [pt1; Lf (TK ArrowT); pt]’ >>
      simp[cmlG_FDOM, cmlG_applied, DISJ_IMP_THM])
  >- (nailIHx (Q.X_CHOOSE_THEN ‘pt’ strip_assume_tac) >>
      rename [‘ptree_head pt1 = NN nDType’] >>
      qexists_tac ‘Nd (mkNT nPType) [pt1; Lf (TK StarT); pt]’ >>
      simp[cmlG_FDOM, cmlG_applied, DISJ_IMP_THM])
  >- (rename [‘ptree_head pt1 = NN nDType’, ‘ptree_head pt2 = NN nTyOp’] >>
      qexists_tac ‘Nd (mkNT nPType) [Nd (mkNT nDType) [pt1; pt2]]’ >>
      simp[cmlG_FDOM, cmlG_applied, DISJ_IMP_THM]));

(*
val simple_SUBSET_actual = Q.store_thm(
  "simple_SUBSET_actual",
  ‘∀pt.
     valid_ptree scmlG pt ⇒
     ∀N s. ptree_head pt = NT (INL N) ∧ ptree_fringe pt = MAP TOK s ⇒
           ∃pt' M.
             valid_ptree cmlG pt' ∧ ptree_head pt' = NT (mkNT M) ∧
             correspondingNT M = SOME N ∧ ptree_fringe pt' = MAP TOK s’,
  ho_match_mp_tac gen_valid_ptree_ind >> conj_tac >> simp[] >>
  rpt strip_tac >> rveq >>
  rename [`correspondingNT _ = SOME N`] >> Cases_on `N` >>
  fs[scmlG_applied, scmlG_FDOM] >> rveq >> fs[] >> rveq >>
  fs[MAP_EQ_CONS, MAP_EQ_APPEND] >> rveq >>
  fs[MAP_EQ_CONS, MAP_EQ_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
  (rename1 `$!` ORELSE
   dsimp[Once ptree_head_EQ_NT, cmlG_FDOM, cmlG_applied])
  >- metis_tac[]
  >- (check "nTypeName" >>
      dsimp[Once ptree_head_EQ_NT, cmlG_FDOM, cmlG_applied] >>
      fs[MAP_EQ_CONS] >> rveq >> dsimp[] >> fs[MAP_EQ_CONS] >>
      fs[DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_APPEND] >> rveq >> dsimp[] >>
      metis_tac[])
  >- (check "nTypeName" >>
      dsimp[Once ptree_head_EQ_NT, cmlG_FDOM, cmlG_applied] >>
      fs[MAP_EQ_CONS] >> rveq >> dsimp[] >>
      fs[MAP_EQ_CONS, DISJ_IMP_THM, FORALL_AND_THM] >> metis_tac[])
  >- (check "nTypeList2" >>
      dsimp[Once ptree_head_EQ_NT, cmlG_applied, cmlG_FDOM] >>
      fs[MAP_EQ_CONS] >> rveq >> dsimp[] >>
      fs[MAP_EQ_APPEND, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
      rveq >> fs[MAP_EQ_CONS] >> rveq >> fs[] >>
      metis_tac[inject_nType])
  >- metis_tac[inject_nType]
  >- (check "nTypeList1" >>
      dsimp[Once ptree_head_EQ_NT, cmlG_applied, cmlG_FDOM] >>
      fs[MAP_EQ_CONS] >> rveq >> dsimp[] >>
      fs[DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_APPEND, PULL_EXISTS,
         MAP_EQ_CONS] >> fs[] >>
      metis_tac[inject_nType])
  >- (check "nTypeDec" >>
      dsimp[Once ptree_head_EQ_NT, cmlG_applied, cmlG_FDOM, MAP_EQ_CONS] >>
      fs[] >> metis_tac[])
  >- (check "nTypeAbbrevDec" >>
      dsimp[Once ptree_head_EQ_NT, cmlG_applied, cmlG_FDOM, MAP_EQ_CONS] >>
      rveq >> metis_tac[inject_nType])
  >- metis_tac[]
  >- (rveq >> CONV_TAC SWAP_VARS_CONV >>
      qexists_tac `nTbase` >>
      dsimp[Once ptree_head_EQ_NT, cmlG_FDOM, cmlG_applied, MAP_EQ_CONS] >>
      metis_tac[])
  >- (check "snType" >> rveq >> CONV_TAC SWAP_VARS_CONV >>
      qexists_tac `nTbase` >>
      dsimp[Once ptree_head_EQ_NT, cmlG_FDOM, cmlG_applied, MAP_EQ_CONS] >>
      metis_tac[inject_nType])
  >- (check "snType" >> rveq >> fs[] >>
      rename [‘correspondingNT NT1 = SOME snType’,
              ‘ptree_head pt1 = NN NT1’] >>
      Cases_on ‘NT1’ >> fs[]
      >- (rename [‘ptree_head _ = NN nType’] >>
          metis_tac[correspondingNT_def, type_nTyOp_parses_to_nType, IN_INSERT])
      >- (rename [‘ptree_head pt1 = NN nTbase’,
                  ‘ptree_head pt2 = NN nTyOp’] >>
          qexists_tac ‘Nd (mkNT nDType) [Nd (mkNT nDType) [pt1]; pt2]’ >>
          simp[cmlG_FDOM, cmlG_applied, DISJ_IMP_THM])
      >- (rename [‘ptree_head _ = NN nPType’] >>
          metis_tac[correspondingNT_def, type_nTyOp_parses_to_nType, IN_INSERT])
      >- (rename [‘ptree_head pt1 = NN nDType’,
                  ‘ptree_head pt2 = NN nTyOp’] >>
          qexists_tac ‘Nd (mkNT nDType) [pt1; pt2]’ >>
          simp[cmlG_FDOM, cmlG_applied, DISJ_IMP_THM])) >>
  cheat)
*)
val _ = export_theory()
