open HolKernel Parse boolLib bossLib

open gramTheory pegexecTheory

local open monadsyntax in end

val _ = new_theory "mmlPEG"



val distinct_ths = let
  val ntlist = TypeBase.constructors_of ``:MMLnonT``
  fun recurse [] = []
    | recurse (t::ts) = let
      val eqns = map (fn t' => mk_eq(t,t')) ts
      val ths0 = map (SIMP_CONV (srw_ss()) []) eqns
      val ths1 = map (CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ))) ths0
    in
      ths0 @ ths1 @ recurse ts
    end
in
  recurse ntlist
end


val _ = computeLib.add_thms distinct_ths computeLib.the_compset

val sumID_def = Define`
  sumID (INL x) = x ∧
  sumID (INR y) = y
`;

val mk_linfix_def = Define`
  mk_linfix tgt acc [] = acc ∧
  mk_linfix tgt acc (opt::t::rest) =
    mk_linfix tgt (Nd tgt [acc; opt; t]) rest
`;

val mk_rinfix_def = Define`
  mk_rinfix tgt [t] = Nd tgt [t] ∧
  mk_rinfix tgt (t::opt::rest) = Nd tgt [t; opt; mk_rinfix tgt rest]`;

val peg_linfix_def = Define`
  peg_linfix tgtnt rptsym opsym =
    seq rptsym (rpt (seq opsym rptsym (++)) FLAT)
        (λa b. [mk_linfix tgtnt (Nd tgtnt [HD a]) b])
`;

val mktokLf_def = Define`mktokLf t = [Lf (TK t)]`
val bindNT_def = Define`
  bindNT ntnm l = [Nd (mkNT ntnm) l]
`

val pegf_def = Define`pegf sym f = seq sym (empty []) (λl1 l2. f l1)`

val choicel_def = Define`
  choicel [] = not (empty ARB) ARB ∧
  choicel (h::t) = choice h (choicel t) sumID
`;

val seql_def = Define`
  seql l f = pegf (FOLDR (\p acc. seq p acc (++)) (empty []) l) f
`;

val peg_nonfix_def = Define`
  peg_nonfix tgtnt argsym opsym =
    seql [argsym; choicel [seq opsym argsym (++); empty []]] (bindNT tgtnt)
`

val try_def = Define`
  try sym = choicel [sym; empty []]
`

val tokeq_def = Define`tokeq t = tok ((=) t) mktokLf`

val pnt_def = Define`pnt ntsym = nt (mkNT ntsym) I`

(* ----------------------------------------------------------------------
    PEG for types
   ---------------------------------------------------------------------- *)

val peg_Type_def = Define`
  peg_Type = seq (pnt nDType)
                 (choice (seq (tokeq ArrowT) (pnt nType) (++))
                         (empty [])
                         sumID)
                 (λa b. case b of
                          [] => [Nd (mkNT nType) a]
                        | _ => [Nd (mkNT nType) [HD a; HD b; HD (TL b)]])
`;

val peg_TyOp_def = Define`
  peg_TyOp = tok isAlphaSym (λt. [Nd (mkNT nTyOp) [Lf (TK t)]])`

val splitAt_def = Define`
  splitAt x [] = ([], []) ∧
  splitAt x (h::t) = if x = h then ([], h::t)
                     else let (pfx,s) = splitAt x t
                          in
                            (h::pfx,s)
`

val calcTyOp_def = Define`
  calcTyOp a b =
    case b of
      [Lf (TK RparT)] => [Nd (mkNT nDType) [Lf (TK LparT); HD a; HD b]]
    | Lf (TK RparT)::ops => FOLDL (λacc opn. [Nd (mkNT nDType) (acc ++ [opn])])
                                  [Lf (TK LparT); Nd (mkNT nTypeList) a; HD b]
                                  ops
    | _ => let (tylist, paren_ops) = splitAt (Lf (TK RparT)) b
           in
             let tylist_n = mk_rinfix (mkNT nTypeList) (HD a :: tylist)
             in
               FOLDL (λacc opn. [Nd (mkNT nDType) (acc ++ [opn])])
                     [Lf (TK LparT); tylist_n; Lf (TK RparT)]
                     (TL paren_ops)
`;

val peg_DType_def = Define`
  (* TyvarT | TyOp | "(" Type ( ")" TyOp* | ("," Type)* ")" TyOp TyOp* ) *)
  peg_DType =
    choice
      (seq (tok isTyvarT (λx. [Nd (mkNT nDType) (mktokLf x)]))
           (rpt (pnt nTyOp) FLAT)
           (λa ops. FOLDL (λacc opn. [Nd (mkNT nDType) (acc ++ [opn])])
                          a ops))
      (choice
        (seq (pegf (pnt nTyOp) (bindNT nDType))
             (rpt (pnt nTyOp) FLAT)
             (λa ops. FOLDL (λacc opn. [Nd (mkNT nDType) (acc ++ [opn])])
                            a ops))
        (seq (tokeq LparT)
             (seq (pnt nType)
                  (choice
                     (* ")" TyOp* *)
                     (seql [tokeq RparT; rpt (pnt nTyOp) FLAT] I)
                     (* ("," Type)* ")" TyOp TyOp* *)
                     (seql [rpt (seql [tokeq CommaT; pnt nType] I) FLAT;
                            tokeq RparT; pnt nTyOp; rpt (pnt nTyOp) FLAT] I)
                     sumID)
                  calcTyOp)
             (λa b. b))
        sumID)
      sumID
`;

val peg_TypeName_def = Define`
  peg_TypeName =
    choicel [pegf (pnt nUQTyOp) (bindNT nTypeName);
             seql [tokeq LparT;
                   peg_linfix (mkNT nTyVarList)
                              (tok isTyvarT mktokLf)
                              (tokeq CommaT);
                   tokeq RparT;
                   pnt nUQTyOp] (bindNT nTypeName);
             seql [tok isTyvarT mktokLf; pnt nUQTyOp] (bindNT nTypeName)
            ]
`;

val peg_UQConstructorName_def = Define`
  peg_UQConstructorName =
    tok (λt. do s <- destAlphaT t ;
                assert (s ≠ "" ∧ isUpper (HD s) ∨ s ∈ {"true"; "false"; "ref"})
             od = SOME ())
        (bindNT nUQConstructorName o mktokLf)
`;

val peg_TypeDec_def = Define`
  peg_TypeDec =
    seq (tokeq DatatypeT)
        (peg_linfix (mkNT nDtypeDecls) (pnt nDtypeDecl)
                    (tokeq AndT))
        (λl1 l2. [Nd (mkNT nTypeDec) (l1 ++ l2)])
`;

(* expressions *)
val peg_V_def = Define`
  peg_V =
   choice (tok (λt.
                  do s <- destAlphaT t;
                     assert(s ∉ {"before"; "div"; "mod"; "o";
                                 "true"; "false";"ref"} ∧
                            s ≠ "" ∧ ¬isUpper (HD s))
                  od = SOME ())
               mktokLf)
          (tok (λt.
                  do s <- destSymbolT t;
                     assert(s ∉ {"+"; "-"; "/"; "<"; ">"; "<="; ">="; "<>";
                                 ":="})
                  od = SOME ())
               mktokLf)
          (bindNT nV o sumID)
`

val peg_Eapp_def = Define`
  peg_Eapp =
    choice (seql [pnt nConstructorName; pnt nEtuple] (bindNT nEapp))
           (seq (pnt nEbase)
                (rpt (pnt nEbase) FLAT)
                (λa b. [FOLDL (λa b. Nd (mkNT nEapp) [a; b])
                              (Nd (mkNT nEapp) [HD a])
                              b]))
           sumID
`;

val mmlPEG_def = zDefine`
  mmlPEG = <|
    start := pnt nDecl;
    rules := FEMPTY |++
             [(mkNT nV, peg_V);
              (mkNT nVlist1,
               seql [pnt nV; rpt (pnt nV) FLAT]
                    (λl. [FOLDR (λe acc. Nd (mkNT nVlist1) [e; acc])
                                (Nd (mkNT nVlist1) [LAST l])
                                (FRONT l)]));
              (mkNT nFQV, pegf (pnt nV) (bindNT nFQV));
              (mkNT nEapp, peg_Eapp);
              (mkNT nEtuple,
               seql [tokeq LparT; pnt nElist2; tokeq RparT] (bindNT nEtuple));
              (mkNT nElist2,
               seql [pnt nE; tokeq CommaT; pnt nElist1] (bindNT nElist2));
              (mkNT nElist1, peg_linfix (mkNT nElist1) (pnt nE) (tokeq CommaT));
              (mkNT nMultOps,
               pegf (choicel (MAP tokeq
                                  [StarT; SymbolT "/"; AlphaT "mod"; AlphaT "div"]))
                    (bindNT nMultOps));
              (mkNT nAddOps,
               pegf (choicel [tokeq (SymbolT "+"); tokeq (SymbolT "-")])
                    (bindNT nAddOps));
              (mkNT nRelOps, pegf (choicel (tok ((=) EqualsT) mktokLf ::
                                            MAP (tokeq o SymbolT)
                                                ["<"; ">"; "<="; ">="; "<>"]))
                                  (bindNT nRelOps));
              (mkNT nCompOps, pegf (choicel [tokeq (SymbolT ":=");
                                             tokeq (AlphaT "o")])
                                   (bindNT nCompOps));
              (mkNT nEbase,
               choicel [tok isInt (bindNT nEbase o mktokLf);
                        pegf (pnt nFQV) (bindNT nEbase);
                        pegf (pnt nConstructorName) (bindNT nEbase);
                        seql [tokeq LparT; tokeq RparT] (bindNT nEbase);
                        seql [tokeq LparT; pnt nEseq; tokeq RparT]
                             (bindNT nEbase);
                        seql [tokeq LetT; pnt nLetDecs; tokeq InT; pnt nEseq;
                              tokeq EndT]
                             (bindNT nEbase)]);
              (mkNT nEseq,
               peg_linfix (mkNT nEseq) (pnt nE) (tokeq SemicolonT));
              (mkNT nEmult,
               peg_linfix (mkNT nEmult) (pnt nEapp) (pnt nMultOps));
              (mkNT nEadd, peg_linfix (mkNT nEadd) (pnt nEmult) (pnt nAddOps));
              (mkNT nErel, peg_nonfix nErel (pnt nEadd) (pnt nRelOps));
              (mkNT nEcomp, peg_linfix (mkNT nEcomp) (pnt nErel)
                                       (pnt nCompOps));
              (mkNT nEbefore, peg_linfix (mkNT nEbefore) (pnt nEcomp)
                                         (tokeq (AlphaT "before")));
              (mkNT nEtyped, seql [pnt nEbefore;
                                   try (seql [tokeq ColonT; pnt nType] I)]
                                  (bindNT nEtyped));
              (mkNT nElogicAND,
               peg_linfix (mkNT nElogicAND) (pnt nEtyped)
                          (tokeq AndalsoT));
              (mkNT nElogicOR,
               peg_linfix (mkNT nElogicOR) (pnt nElogicAND)
                          (tokeq OrelseT));
              (mkNT nE,
               choicel [seql [tokeq RaiseT; pnt nE] (bindNT nE);
                        pegf (pnt nElogicOR) (bindNT nE);
                        seql [tokeq IfT; pnt nE; tokeq ThenT; pnt nE;
                              tokeq ElseT; pnt nE]
                             (bindNT nE);
                        seql [tokeq FnT; pnt nV; tokeq DarrowT; pnt nE]
                             (bindNT nE);
                        seql [tokeq CaseT; pnt nE; tokeq OfT; pnt nPEs]
                             (bindNT nE)]);
              (mkNT nPEs, peg_linfix (mkNT nPEs) (pnt nPE) (tokeq BarT));
              (mkNT nPE, seql [pnt nPattern; tokeq DarrowT; pnt nE]
                              (bindNT nPE));
              (mkNT nAndFDecls,
               peg_linfix (mkNT nAndFDecls) (pnt nFDecl) (tokeq AndT));
              (mkNT nFDecl,
               seql [pnt nV; pnt nVlist1; tokeq EqualsT; pnt nE]
                    (bindNT nFDecl));
              (mkNT nType, peg_Type);
              (mkNT nDType, peg_DType);
              (mkNT nTyOp, peg_TyOp);
              (mkNT nUQTyOp, tok isAlphaSym (bindNT nUQTyOp o mktokLf));
              (mkNT nStarTypes,
               peg_linfix (mkNT nStarTypes) (pnt nDType) (tokeq StarT));
              (mkNT nStarTypesP,
               choicel [seql [tokeq LparT; pnt nStarTypes; tokeq RparT]
                             (bindNT nStarTypesP);
                        pegf (pnt nStarTypes) (bindNT nStarTypesP)]);
              (mkNT nTypeName, peg_TypeName);
              (mkNT nTypeDec, peg_TypeDec);
              (mkNT nDtypeDecl,
               seql [pnt nTypeName;
                     tokeq EqualsT;
                     peg_linfix (mkNT nDtypeCons) (pnt nDconstructor) (tokeq BarT)]
                    (bindNT nDtypeDecl));
              (mkNT nDconstructor,
               seql [pnt nUQConstructorName;
                     try (seql [tokeq OfT; pnt nStarTypesP] I)]
                    (bindNT nDconstructor));
              (mkNT nUQConstructorName, peg_UQConstructorName);
              (mkNT nConstructorName,
               pegf (pnt nUQConstructorName) (bindNT nConstructorName));
              (mkNT nPbase,
               pegf (choicel [pnt nV;
                              pnt nConstructorName;
                              tok isInt mktokLf;
                              tokeq UnderbarT;
                              seql [tokeq LparT; tokeq RparT] I;
                              seql [tokeq LparT; pnt nPattern; tokeq RparT] I])
                    (bindNT nPbase));
              (mkNT nPattern,
               pegf (choicel [seql [pnt nConstructorName;
                                    choicel [pnt nPtuple; pnt nPbase]] I;
                              pnt nPbase])
                    (bindNT nPattern));
              (mkNT nPtuple, seql [tokeq LparT; pnt nPatternList2; tokeq RparT]
                                  (bindNT nPtuple));
              (mkNT nPatternList2,
               seql [pnt nPattern; tokeq CommaT; pnt nPatternList1]
                    (bindNT nPatternList2));
              (mkNT nPatternList1,
               peg_linfix (mkNT nPatternList1) (pnt nPattern) (tokeq CommaT));
              (mkNT nLetDec,
               choicel [seql [tokeq ValT; pnt nV; tokeq EqualsT; pnt nE]
                             (bindNT nLetDec);
                        seql [tokeq FunT; pnt nAndFDecls]
                             (bindNT nLetDec);
                        pegf (tokeq SemicolonT) (bindNT nLetDec)]);
              (mkNT nLetDecs,
               rpt (pnt nLetDec)
                   (λds. [FOLDR (λd acc. Nd (mkNT nLetDecs) [HD d; acc])
                                (Nd (mkNT nLetDecs) [])
                                ds]));
              (mkNT nDecl,
               choicel [seql [tokeq ValT; pnt nPattern; tokeq EqualsT; pnt nE]
                             (bindNT nDecl);
                        seql [tokeq FunT; pnt nAndFDecls] (bindNT nDecl);
                        seql [pnt nTypeDec] (bindNT nDecl);
                        pegf (tokeq SemicolonT) (bindNT nDecl)]);
              (mkNT nDecls,
               rpt (pnt nDecl)
                   (λds. [FOLDR (λd acc. Nd (mkNT nDecls) [HD d; acc])
                                (Nd (mkNT nDecls) [])
                                ds]))
             ] |>
`;

val rules_t = ``mmlPEG.rules``
val rules = SIMP_CONV (srw_ss()) [mmlPEG_def] rules_t

val _ = print "Calculating application of mmlPEG rules - "
val mmlpeg_rules_applied = let
  val app0 = finite_mapSyntax.fapply_t
  val theta =
      Type.match_type (type_of app0 |> dom_rng |> #1) (type_of rules_t)
  val app = inst theta app0
  val app_rules = AP_TERM app rules
  fun mkrule t =
      AP_THM app_rules ``mkNT ^t``
             |> SIMP_RULE (srw_ss()) [finite_mapTheory.FUPDATE_LIST,
                                      finite_mapTheory.FAPPLY_FUPDATE_THM]
in
    TypeBase.constructors_of ``:MMLnonT`` |> map mkrule
end
val _ = print "done\n"

val peg_dom =
    SIMP_CONV (srw_ss()) [mmlPEG_def,
                          finite_mapTheory.FRANGE_FUPDATE_DOMSUB,
                          finite_mapTheory.DOMSUB_FUPDATE_THM,
                          finite_mapTheory.FUPDATE_LIST_THM] ``FDOM mmlPEG.rules``

val spec0 =
    peg_nt_thm |> Q.GEN `G`  |> Q.ISPEC `mmlPEG`
               |> SIMP_RULE (srw_ss()) [peg_dom]
               |> Q.GEN `n`

val mkNT = ``mkNT``

val mmlPEG_exec_thm = save_thm(
  "mmlPEG_exec_thm",
  TypeBase.constructors_of ``:MMLnonT``
    |> map (fn t => ISPEC (mk_comb(mkNT, t)) spec0)
    |> map (SIMP_RULE (srw_ss()) mmlpeg_rules_applied)
    |> LIST_CONJ)
val _ = computeLib.add_persistent_funs ["mmlPEG_exec_thm"]

val test1 = time EVAL ``peg_exec mmlPEG (pnt nErel) [IntT 3; StarT; IntT 4; SymbolT "/"; IntT (-2); SymbolT ">"; AlphaT "x"] [] done failed``


open lcsymtacs

val frange_image = prove(
  ``FRANGE fm = IMAGE (FAPPLY fm) (FDOM fm)``,
  simp[finite_mapTheory.FRANGE_DEF, pred_setTheory.EXTENSION] >> metis_tac[]);

val peg_range =
    SIMP_CONV (srw_ss())
              (peg_dom :: frange_image :: mmlpeg_rules_applied)
              ``FRANGE mmlPEG.rules``

val peg_start = SIMP_CONV(srw_ss()) [mmlPEG_def]``mmlPEG.start``

val wfpeg_rwts = pegTheory.wfpeg_cases
                   |> ISPEC ``mmlPEG``
                   |> (fn th => map (fn t => Q.SPEC t th)
                                    [`seq e1 e2 f`, `choice e1 e2 f`, `tok P f`,
                                     `any f`, `empty v`, `not e v`, `rpt e f`,
                                     `choicel []`, `choicel (h::t)`, `tokeq t`,
                                     `pegf e f`
                      ])
                   |> map (CONV_RULE
                             (RAND_CONV (SIMP_CONV (srw_ss())
                                                   [choicel_def, seql_def, tokeq_def,
                                                    pegf_def])))

val wfpeg_pnt = pegTheory.wfpeg_cases
                  |> ISPEC ``mmlPEG``
                  |> Q.SPEC `pnt n`
                  |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [pnt_def]))

val peg0_rwts = pegTheory.peg0_cases
                  |> ISPEC ``mmlPEG`` |> CONJUNCTS
                  |> map (fn th => map (fn t => Q.SPEC t th)
                                       [`tok P f`, `choice e1 e2 f`, `seq e1 e2 f`,
                                        `tokeq t`, `empty l`, `not e v`])
                  |> List.concat
                  |> map (CONV_RULE
                            (RAND_CONV (SIMP_CONV (srw_ss())
                                                  [tokeq_def])))

val pegnt_case_ths = pegTheory.peg0_cases
                      |> ISPEC ``mmlPEG`` |> CONJUNCTS
                      |> map (Q.SPEC `pnt n`)
                      |> map (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [pnt_def])))

fun pegnt(t,acc) = let
  val th =
      prove(``¬peg0 mmlPEG (pnt ^t)``,
            simp(pegnt_case_ths @ mmlpeg_rules_applied @
                 [peg_dom, peg_V_def, peg_UQConstructorName_def, peg_TypeName_def,
                  peg_TypeDec_def, choicel_def, seql_def,
                  peg_TyOp_def, pegf_def, peg_linfix_def,
                  peg_DType_def, peg_Eapp_def]) >>
            simp(peg0_rwts @ acc))
in
  th::acc
end

val npeg0_rwts =
    List.foldl pegnt []
               [``nTypeDec``, ``nDecl``, ``nV``, ``nVlist1``, ``nUQTyOp``,
                ``nUQConstructorName``, ``nConstructorName``, ``nTypeName``,
                ``nTyOp``, ``nDType``, ``nStarTypes``, ``nStarTypesP``,
                ``nRelOps``, ``nPtuple``, ``nPbase``, ``nPattern``, ``nLetDec``,
                ``nFQV``, ``nAddOps``, ``nCompOps``, ``nEbase``, ``nEapp``]

fun wfnt(t,acc) = let
  val th =
    prove(``wfpeg mmlPEG (pnt ^t)``,
          SIMP_TAC (srw_ss()) (mmlpeg_rules_applied @
                               [wfpeg_pnt, peg_dom, try_def,
                                seql_def, peg_TypeDec_def, peg_V_def, peg_Type_def,
                                peg_UQConstructorName_def, peg_TypeName_def,
                                peg_TyOp_def, peg_DType_def, peg_nonfix_def,
                                tokeq_def, peg_linfix_def, peg_Eapp_def]) THEN
          simp(wfpeg_rwts @ npeg0_rwts @ peg0_rwts @ acc))
in
  th::acc
end;

val topo_nts = [``nV``, ``nTypeDec``, ``nDecl``, ``nVlist1``,
                ``nUQTyOp``, ``nUQConstructorName``,
                ``nConstructorName``, ``nTypeName``, ``nTyOp``, ``nDType``,
                ``nStarTypes``, ``nStarTypesP``,
                ``nRelOps``, ``nPtuple``, ``nPbase``, ``nPattern``, ``nPE``,
                ``nPEs``, ``nMultOps``, ``nLetDec``, ``nLetDecs``, ``nFQV``,
                ``nFDecl``, ``nAddOps``, ``nCompOps``, ``nEbase``, ``nEapp``,
                ``nEmult``, ``nEadd``, ``nErel``,
                ``nEcomp``, ``nEbefore``, ``nEtyped``, ``nElogicAND``,
                ``nElogicOR``, ``nE``, ``nType``,
                ``nPatternList1``, ``nPatternList2``,
                ``nEtuple``, ``nEseq``, ``nElist1``, ``nElist2``, ``nDtypeDecl``,
                ``nDecls``, ``nDconstructor``, ``nAndFDecls``]

val cml_wfpeg_thm = save_thm(
  "cml_wfpeg_thm",
  LIST_CONJ (List.foldl wfnt [] topo_nts))

(*
set_diff (TypeBase.constructors_of ``:MMLnonT``)
         (topo_nts @ [``nTyVarList``, ``nTypeList``, ``nDtypeDecls``,
                      ``nDtypeCons``])
*)

val subexprs_pnt = prove(
  ``subexprs (pnt n) = {pnt n}``,
  simp[pegTheory.subexprs_def, pnt_def]);

val PEG_wellformed = store_thm(
  "PEG_wellformed",
  ``wfG mmlPEG``,
  simp[pegTheory.wfG_def, pegTheory.Gexprs_def, pegTheory.subexprs_def,
       subexprs_pnt, peg_start, peg_range, DISJ_IMP_THM, FORALL_AND_THM,
       choicel_def, seql_def, pegf_def, tokeq_def, try_def,
       peg_linfix_def, peg_UQConstructorName_def, peg_TypeDec_def,
       peg_TypeName_def, peg_V_def, peg_Eapp_def, peg_nonfix_def, peg_Type_def,
       peg_DType_def, peg_TyOp_def] >>
  simp(cml_wfpeg_thm :: wfpeg_rwts @ peg0_rwts @ npeg0_rwts));

val _ = export_theory()
