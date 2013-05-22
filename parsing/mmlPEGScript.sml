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
  mk_linfix tgt acc [t] = acc ∧
  mk_linfix tgt acc (opt::t::rest) =
    mk_linfix tgt (Nd tgt [acc; opt; t]) rest
`;

val mk_rinfix_def = Define`
  mk_rinfix tgt [] = Nd tgt [] ∧
  mk_rinfix tgt [t] = Nd tgt [t] ∧
  mk_rinfix tgt (t::opt::rest) = Nd tgt [t; opt; mk_rinfix tgt rest]`;

val peg_linfix_def = Define`
  peg_linfix tgtnt rptsym opsym =
    seq rptsym (rpt (seq opsym rptsym (++)) FLAT)
        (λa b. case a of
                   [] => []
                  | h::_ => [mk_linfix tgtnt (Nd tgtnt [h]) b])
`;

val mktokLf_def = Define`mktokLf t = [Lf (TK t)]`
val bindNT_def = Define`
  bindNT ntnm l = [Nd (mkNT ntnm) l]
`

val pegf_def = Define`pegf sym f = seq sym (empty []) (λl1 l2. f l1)`

val choicel_def = Define`
  choicel [] = not (empty []) [] ∧
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
                 (λa b. case (a,b) of
                          (_, []) => [Nd (mkNT nType) a]
                        | ([], _) => [] (* shouldn't happen *)
                        | (_, [b]) => [] (* shouldn't happen *)
                        | (ah::at, b1::b2::bt) =>
                          [Nd (mkNT nType) [ah; b1; b2]])
`;

val calcTyOp_def = Define`
  calcTyOp a b =
    if b = [Lf (TK RparT)] then
      (case a of
           [] => []
         | ah::_ => [Nd (mkNT nDType) [Lf (TK LparT); ah; Lf (TK RparT)]])
    else if b ≠ [] /\ HD b = Lf (TK RparT) then
      let ops = TL b in
        FOLDL (λacc opn. [Nd (mkNT nDType) (acc ++ [opn])])
              [Lf (TK LparT); Nd (mkNT nTypeList) a; Lf (TK RparT)]
              ops
    else let (tylist, paren_ops) = splitAtPki (K ((=) (Lf (TK RparT)))) (,) b
         in
           case (a,paren_ops) of
               ([],_) => []  (* shouldn't happen *)
             | (_,[]) => []  (* shouldn't happen *)
             | (ah::_,_::pt) =>
               let tylist_n = mk_rinfix (mkNT nTypeList) (ah :: tylist)
               in
                 FOLDL (λacc opn. [Nd (mkNT nDType) (acc ++ [opn])])
                       [Lf (TK LparT); tylist_n; Lf (TK RparT)]
                       pt
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
                (λa b.
                    case a of
                        [] => []
                      | ah::_ =>
                        [FOLDL (λa b. Nd (mkNT nEapp) [a; b])
                               (Nd (mkNT nEapp) [ah]) b]))
           sumID
`;

val peg_longV_def = Define`
  peg_longV = tok (λt. do
                        (str,s) <- destLongidT t;
                        assert(s <> "" ∧ (isAlpha (HD s) ⇒ ¬isUpper (HD s)))
                       od = SOME ())
                  (bindNT nFQV o mktokLf)
`

val mmlPEG_def = zDefine`
  mmlPEG = <|
    start := pnt nREPLTop;
    rules := FEMPTY |++
             [(mkNT nV, peg_V);
              (mkNT nVlist1,
               seql [pnt nV; rpt (pnt nV) FLAT]
                    (λl. if l = [] then []
                         else [FOLDR (λe acc. Nd (mkNT nVlist1) [e; acc])
                                       (Nd (mkNT nVlist1) [LAST l])
                                       (FRONT l)]));
              (mkNT nFQV, choicel [pegf (pnt nV) (bindNT nFQV); peg_longV]);
              (mkNT nExn,
               pegf (choicel
                       [tokeq (AlphaT "Bind");
                        tokeq (AlphaT "Div");
                        seql [tokeq (AlphaT "IntError"); tok isInt mktokLf] I])
                    (bindNT nExn));
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
              (mkNT nEhandle,
               seql [pnt nElogicOR;
                     try (seql [tokeq HandleT; tokeq (AlphaT "IntError"); pnt nV;
                                tokeq DarrowT; pnt nE] I)]
                    (bindNT nEhandle)
              );
              (mkNT nE,
               choicel [seql [tokeq RaiseT; pnt nExn] (bindNT nE);
                        pegf (pnt nEhandle) (bindNT nE);
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
              (mkNT nTyOp,
               pegf (choicel [pnt nUQTyOp; tok isLongidT mktokLf])
                    (bindNT nTyOp));
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
               choicel [
                 pegf (pnt nUQConstructorName) (bindNT nConstructorName);
                 tok (λt. do
                            (str,s) <- destLongidT t;
                            assert(s <> "" ∧ isAlpha (HD s) ∧
                                   isUpper (HD s))
                          od = SOME ())
                     (bindNT nConstructorName o mktokLf)]);
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
                        seql [tokeq FunT; pnt nAndFDecls] (bindNT nLetDec)]);
              (mkNT nLetDecs,
               choicel [seql [pnt nLetDec; pnt nLetDecs] (bindNT nLetDecs);
                        seql [tokeq SemicolonT; pnt nLetDecs] (bindNT nLetDecs);
                        pegf (empty []) (bindNT nLetDecs)]);
              (mkNT nDecl,
               choicel [seql [tokeq ValT; pnt nPattern; tokeq EqualsT; pnt nE]
                             (bindNT nDecl);
                        seql [tokeq FunT; pnt nAndFDecls] (bindNT nDecl);
                        seql [pnt nTypeDec] (bindNT nDecl)]);
              (mkNT nDecls,
               choicel [seql [pnt nDecl; pnt nDecls] (bindNT nDecls);
                        seql [tokeq SemicolonT; pnt nDecls] (bindNT nDecls);
                        pegf (empty []) (bindNT nDecls)]);
              (mkNT nSpecLine,
               choicel [seql [tokeq ValT; pnt nV; tokeq ColonT; pnt nType]
                             (bindNT nSpecLine);
                        seql [tokeq TypeT; pnt nV] (bindNT nSpecLine);
                        pegf (pnt nTypeDec) (bindNT nSpecLine)]);
              (mkNT nSpecLineList,
               choicel [seql [pnt nSpecLine; pnt nSpecLineList]
                             (bindNT nSpecLineList);
                        seql [tokeq SemicolonT; pnt nSpecLineList]
                             (bindNT nSpecLineList);
                        pegf (empty []) (bindNT nSpecLineList)]);
              (mkNT nSignatureValue,
               seql [tokeq SigT; pnt nSpecLineList; tokeq EndT]
                    (bindNT nSignatureValue));
              (mkNT nOptionalSignatureAscription,
               pegf (try (seql [tokeq SealT; pnt nSignatureValue] I))
                    (bindNT nOptionalSignatureAscription));
              (mkNT nStructure,
               seql [tokeq StructureT; pnt nV; pnt nOptionalSignatureAscription;
                     tokeq EqualsT; tokeq StructT; pnt nDecls; tokeq EndT]
                    (bindNT nStructure));
              (mkNT nTopLevelDec,
               pegf (choicel [pnt nStructure; pnt nDecl]) (bindNT nTopLevelDec));
              (mkNT nTopLevelDecs,
               rpt (pnt nTopLevelDec)
                   (λtds. [FOLDR
                             (λtd acc.
                                  Nd (mkNT nTopLevelDecs)
                                     (case td of
                                          [] => [acc] (* should't happen *)
                                        | tdh::_ => [tdh; acc]))
                             (Nd (mkNT nTopLevelDecs) []) tds]));
              (mkNT nREPLPhrase,
               choicel [seql [pnt nE; tokeq SemicolonT] (bindNT nREPLPhrase);
                        seql [pnt nTopLevelDecs; tokeq SemicolonT]
                             (bindNT nREPLPhrase)]);
              (mkNT nREPLTop,
               choicel [seql [pnt nE; tokeq SemicolonT] (bindNT nREPLTop);
                        seql [pnt nTopLevelDec; tokeq SemicolonT]
                             (bindNT nREPLTop)])
             ] |>
`;

val rules_t = ``mmlPEG.rules``
fun ty2frag ty = let
  open simpLib
  val {convs,rewrs} = TypeBase.simpls_of ty
in
  merge_ss (rewrites rewrs :: map conv_ss convs)
end
(* can't use srw_ss() as it will attack the bodies of the rules,
   and in particular, will destroy predicates from tok
   constructors of the form
        do ... od = SOME ()
   which matches optionTheory.OPTION_BIND_EQUALS_OPTION, putting
   an existential into our rewrite thereby *)
val rules = SIMP_CONV (bool_ss ++ ty2frag ``:(α,β,γ)peg``)
                      [mmlPEG_def, combinTheory.K_DEF,
                       finite_mapTheory.FUPDATE_LIST_THM] rules_t

val _ = print "Calculating application of mmlPEG rules\n"
val mmlpeg_rules_applied = let
  val app0 = finite_mapSyntax.fapply_t
  val theta =
      Type.match_type (type_of app0 |> dom_rng |> #1) (type_of rules_t)
  val app = inst theta app0
  val app_rules = AP_TERM app rules
  val sset = bool_ss ++ ty2frag ``:'a + 'b`` ++ ty2frag ``:MMLnonT``
  fun mkrule t =
      AP_THM app_rules ``mkNT ^t``
             |> SIMP_RULE sset
                  [finite_mapTheory.FAPPLY_FUPDATE_THM]
  val ths = TypeBase.constructors_of ``:MMLnonT`` |> map mkrule
in
    save_thm("mmlpeg_rules_applied", LIST_CONJ ths);
    ths
end

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
    |> map (SIMP_RULE bool_ss mmlpeg_rules_applied)
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
                  peg_TypeDec_def, choicel_def, seql_def, peg_longV_def,
                  pegf_def, peg_linfix_def,
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
                ``nFQV``, ``nAddOps``, ``nCompOps``, ``nEbase``, ``nEapp``,
                ``nSpecLine``, ``nStructure``, ``nTopLevelDec``]

fun wfnt(t,acc) = let
  val th =
    prove(``wfpeg mmlPEG (pnt ^t)``,
          SIMP_TAC (srw_ss()) (mmlpeg_rules_applied @
                               [wfpeg_pnt, peg_dom, try_def, peg_longV_def,
                                seql_def, peg_TypeDec_def, peg_V_def, peg_Type_def,
                                peg_UQConstructorName_def, peg_TypeName_def,
                                peg_DType_def, peg_nonfix_def,
                                tokeq_def, peg_linfix_def, peg_Eapp_def]) THEN
          simp(wfpeg_rwts @ npeg0_rwts @ peg0_rwts @ acc))
in
  th::acc
end;

val topo_nts = [``nExn``, ``nV``, ``nTypeDec``, ``nDecl``, ``nVlist1``,
                ``nUQTyOp``, ``nUQConstructorName``,
                ``nConstructorName``, ``nTypeName``, ``nTyOp``, ``nDType``,
                ``nStarTypes``, ``nStarTypesP``,
                ``nRelOps``, ``nPtuple``, ``nPbase``, ``nPattern``, ``nPE``,
                ``nPEs``, ``nMultOps``, ``nLetDec``, ``nLetDecs``, ``nFQV``,
                ``nFDecl``, ``nAddOps``, ``nCompOps``, ``nEbase``, ``nEapp``,
                ``nEmult``, ``nEadd``, ``nErel``,
                ``nEcomp``, ``nEbefore``, ``nEtyped``, ``nElogicAND``,
                ``nElogicOR``, ``nEhandle``, ``nE``, ``nType``,
                ``nPatternList1``, ``nPatternList2``,
                ``nEtuple``, ``nEseq``, ``nElist1``, ``nElist2``, ``nDtypeDecl``,
                ``nDecls``, ``nDconstructor``, ``nAndFDecls``, ``nSpecLine``,
                ``nSpecLineList``, ``nSignatureValue``,
                ``nOptionalSignatureAscription``, ``nStructure``,
                ``nTopLevelDec``, ``nTopLevelDecs``, ``nREPLPhrase``, ``nREPLTop``]

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
       peg_DType_def, peg_longV_def] >>
  simp(cml_wfpeg_thm :: wfpeg_rwts @ peg0_rwts @ npeg0_rwts));

val parse_REPLTop_total = save_thm(
  "parse_REPLTop_total",
  MATCH_MP peg_exec_total PEG_wellformed
           |> REWRITE_RULE [peg_start] |> Q.GEN `i`);

val coreloop_REPLTop_total = save_thm(
  "coreloop_REPLTop_total",
  MATCH_MP coreloop_total PEG_wellformed
    |> REWRITE_RULE [peg_start] |> Q.GEN `i`);

val owhile_REPLTop_total = save_thm(
  "owhile_REPLTop_total",
  SIMP_RULE (srw_ss()) [coreloop_def] coreloop_REPLTop_total);

val _ = export_theory()
