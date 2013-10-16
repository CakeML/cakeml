open HolKernel Parse boolLib bossLib

open gramTheory pegexecTheory

local open monadsyntax in end

fun Store_thm(n,t,tac) = store_thm(n,t,tac) before export_rewrites [n]

val _ = new_theory "cmlPEG"



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

val peg_UQConstructorName_def = Define`
  peg_UQConstructorName =
    tok (λt. do s <- destAlphaT t ;
                assert (s ≠ "" ∧ isUpper (HD s) ∨
                        s ∈ {"true"; "false"; "ref"; "nil"})
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
                                 "true"; "false";"ref";"nil"} ∧
                            s ≠ "" ∧ ¬isUpper (HD s))
                  od = SOME ())
               mktokLf)
          (tok (λt.
                  do s <- destSymbolT t;
                     assert(s ∉ {"+"; "-"; "/"; "<"; ">"; "<="; ">="; "<>";
                                 ":="; "*"; "::"; "@"})
                  od = SOME ())
               mktokLf)
          (bindNT nV o sumID)
`

val peg_longV_def = Define`
  peg_longV = tok (λt. do
                        (str,s) <- destLongidT t;
                        assert(s <> "" ∧ (isAlpha (HD s) ⇒ ¬isUpper (HD s)) ∧
                               s ∉ {"ref"; "true"; "false"; "nil"})
                       od = SOME ())
                  (bindNT nFQV o mktokLf)
`

val peg_EbaseParenFn_def = Define`
  peg_EbaseParenFn l =
    case l of
        [lp; e; rp] =>
        [Nd (mkNT nEbase) [lp; Nd (mkNT nEseq) [e]; rp]]
      | [lp; e; cs; rest; rp] =>
        if cs = Lf (TK CommaT) then
          [
            Nd (mkNT nEbase) [
              Nd (mkNT nEtuple) [lp; Nd (mkNT nElist2) [e; cs; rest]; rp]
            ]
          ]
        else
          [Nd (mkNT nEbase) [lp; Nd (mkNT nEseq) [e; cs; rest]; rp]]
      | _ => []
`

val peg_EbaseParen_def = Define`
  peg_EbaseParen =
    seql [tokeq LparT; pnt nE;
          choicel [tokeq RparT;
                   seql [tokeq CommaT; pnt nElist1; tokeq RparT] I;
                   seql [tokeq SemicolonT; pnt nEseq; tokeq RparT] I]]
         peg_EbaseParenFn
`
val peg_StructName_def = Define`
  peg_StructName =
    tok (λt. do s <- destAlphaT t ;
                assert (s ≠ "")
             od = SOME ())
        (bindNT nStructName o mktokLf)
`;


val cmlPEG_def = zDefine`
  cmlPEG = <|
    start := pnt nREPLTop;
    rules := FEMPTY |++
             [(mkNT nV, peg_V);
              (mkNT nTyvarN, pegf (tok isTyvarT mktokLf) (bindNT nTyvarN));
              (mkNT nVlist1,
               seql [pnt nV; try (pnt nVlist1)] (bindNT nVlist1));
              (mkNT nFQV, choicel [pegf (pnt nV) (bindNT nFQV); peg_longV]);
              (mkNT nEapp,
               seql [pnt nEbase; rpt (pnt nEbase) FLAT]
                    (λl.
                       case l of
                         [] => []
                       | h::t => [FOLDL (λa b. Nd (mkNT nEapp) [a;b])
                                        (Nd (mkNT nEapp) [h]) t]));
              (mkNT nElist1,
               seql [pnt nE; try (seql [tokeq CommaT; pnt nElist1] I)]
                    (bindNT nElist1));
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
              (mkNT nListOps, pegf (choicel (MAP (tokeq o SymbolT) ["::"; "@"]))
                                   (bindNT nListOps));
              (mkNT nCompOps, pegf (choicel [tokeq (SymbolT ":=");
                                             tokeq (AlphaT "o")])
                                   (bindNT nCompOps));
              (mkNT nEbase,
               choicel [tok isInt (bindNT nEbase o mktokLf);
                        seql [tokeq LparT; tokeq RparT] (bindNT nEbase);
                        peg_EbaseParen;
                        seql [tokeq LbrackT; try (pnt nElist1); tokeq RbrackT]
                             (bindNT nEbase);
                        seql [tokeq LetT; pnt nLetDecs; tokeq InT; pnt nEseq;
                              tokeq EndT] (bindNT nEbase);
                        pegf (pnt nFQV) (bindNT nEbase);
                        pegf (pnt nConstructorName) (bindNT nEbase)]);
              (mkNT nEseq,
               seql [pnt nE; try (seql [tokeq SemicolonT; pnt nEseq] I)]
                    (bindNT nEseq));
              (mkNT nEmult,
               peg_linfix (mkNT nEmult) (pnt nEapp) (pnt nMultOps));
              (mkNT nEadd, peg_linfix (mkNT nEadd) (pnt nEmult) (pnt nAddOps));
              (mkNT nElistop,
               seql [pnt nEadd; try (seql [pnt nListOps; pnt nElistop] I)]
                    (bindNT nElistop));
              (mkNT nErel, peg_linfix (mkNT nErel) (pnt nElistop) (pnt nRelOps));
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
                     try (seql [tokeq HandleT; pnt nPEs] I)]
                    (bindNT nEhandle)
              );
              (mkNT nE,
               choicel [seql [tokeq RaiseT; pnt nE] (bindNT nE);
                        pegf (pnt nEhandle) (bindNT nE);
                        seql [tokeq IfT; pnt nE; tokeq ThenT; pnt nE;
                              tokeq ElseT; pnt nE]
                             (bindNT nE);
                        seql [tokeq FnT; pnt nV; tokeq DarrowT; pnt nE]
                             (bindNT nE);
                        seql [tokeq CaseT; pnt nE; tokeq OfT; pnt nPEs]
                             (bindNT nE)]);
              (mkNT nE',
               choicel [seql [tokeq RaiseT; pnt nE'] (bindNT nE');
                        pegf (pnt nElogicOR) (bindNT nE');
                        seql [tokeq IfT; pnt nE; tokeq ThenT; pnt nE;
                              tokeq ElseT; pnt nE'] (bindNT nE')]);
              (mkNT nPEs,
               choicel [seql [pnt nPE'; tokeq BarT; pnt nPEs] (bindNT nPEs);
                        pegf (pnt nPE) (bindNT nPEs)]);
              (mkNT nPE, seql [pnt nPattern; tokeq DarrowT; pnt nE]
                              (bindNT nPE));
              (mkNT nPE', seql [pnt nPattern; tokeq DarrowT; pnt nE']
                               (bindNT nPE'));
              (mkNT nAndFDecls,
               peg_linfix (mkNT nAndFDecls) (pnt nFDecl) (tokeq AndT));
              (mkNT nFDecl,
               seql [pnt nV; pnt nVlist1; tokeq EqualsT; pnt nE]
                    (bindNT nFDecl));
              (mkNT nType,
               seql [pnt nPType; try (seql [tokeq ArrowT; pnt nType] I)]
                    (bindNT nType));
              (mkNT nDType,
               seql [pnt nTbase; rpt (pnt nTyOp) FLAT]
                    (λsubs.
                       case subs of
                           [] => []
                         | h::t => [FOLDL (λa b. Nd (mkNT nDType) [a; b])
                                          (Nd (mkNT nDType) [h]) t]));
              (mkNT nTbase,
               choicel [
                 seql [tokeq LparT; pnt nType; tokeq RparT] (bindNT nTbase);
                 seql [tokeq LparT; pnt nTypeList2; tokeq RparT; pnt nTyOp]
                      (bindNT nTbase);
                 tok isTyvarT (bindNT nTbase o mktokLf);
                 pegf (pnt nTyOp) (bindNT nTbase)
               ]);
              (mkNT nTypeList2,
               seql [pnt nType; tokeq CommaT; pnt nTypeList1]
                    (bindNT nTypeList2));
              (mkNT nTypeList1,
               seql [pnt nType; try (seql [tokeq CommaT; pnt nTypeList1] I)]
                    (bindNT nTypeList1));
              (mkNT nTyOp,
               pegf (choicel [pnt nUQTyOp; tok isLongidT mktokLf])
                    (bindNT nTyOp));
              (mkNT nUQTyOp, tok isAlphaSym (bindNT nUQTyOp o mktokLf));
              (mkNT nPType,
               seql [pnt nDType; try (seql [tokeq StarT; pnt nPType] I)]
                    (bindNT nPType));
              (mkNT nTypeName,
               choicel [pegf (pnt nUQTyOp) (bindNT nTypeName);
                        seql [tokeq LparT; pnt nTyVarList;
                              tokeq RparT; pnt nUQTyOp] (bindNT nTypeName);
                        seql [tok isTyvarT mktokLf; pnt nUQTyOp]
                             (bindNT nTypeName)
                       ]);
              (mkNT nTyVarList,
               peg_linfix (mkNT nTyVarList) (pnt nTyvarN) (tokeq CommaT));
              (mkNT nTypeDec, peg_TypeDec);
              (mkNT nDtypeDecl,
               seql [pnt nTypeName;
                     tokeq EqualsT;
                     peg_linfix (mkNT nDtypeCons) (pnt nDconstructor) (tokeq BarT)]
                    (bindNT nDtypeDecl));
              (mkNT nDconstructor,
               seql [pnt nUQConstructorName;
                     try (seql [tokeq OfT; pnt nType] I)]
                    (bindNT nDconstructor));
              (mkNT nUQConstructorName, peg_UQConstructorName);
              (mkNT nConstructorName,
               choicel [
                 pegf (pnt nUQConstructorName) (bindNT nConstructorName);
                 tok (λt. do
                            (str,s) <- destLongidT t;
                            assert(s <> "" ∧ isAlpha (HD s) ∧
                                   isUpper (HD s) ∨
                                   s ∈ {"ref"; "true"; "false"; "nil"})
                          od = SOME ())
                     (bindNT nConstructorName o mktokLf)]);
              (mkNT nPbase,
               pegf
                 (choicel [pnt nV; pnt nConstructorName; tok isInt mktokLf;
                           pnt nPtuple; tokeq UnderbarT;
                           seql [tokeq LbrackT; try (pnt nPatternList);
                                 tokeq RbrackT] I])
                 (bindNT nPbase));
              (mkNT nPapp,
               (* could be optimised so that a bare constructor name doesn't
                  cause a backtrack *)
               choicel [seql [pnt nConstructorName; pnt nPbase]
                             (bindNT nPapp);
                        pegf (pnt nPbase) (bindNT nPapp)]);
              (mkNT nPattern,
               seql [pnt nPapp;
                     try (seql [tokeq (SymbolT "::"); pnt nPattern] I)]
                    (bindNT nPattern));
              (mkNT nPatternList,
               seql [pnt nPattern;
                     try (seql [tokeq CommaT; pnt nPatternList] I)]
                    (bindNT nPatternList));
              (mkNT nPtuple,
               choicel [seql [tokeq LparT; tokeq RparT] (bindNT nPtuple);
                        seql [tokeq LparT; pnt nPatternList; tokeq RparT]
                             (bindNT nPtuple)]);
              (mkNT nLetDec,
               choicel [seql [tokeq ValT; pnt nV; tokeq EqualsT; pnt nE]
                             (bindNT nLetDec);
                        seql [tokeq FunT; pnt nAndFDecls] (bindNT nLetDec)]);
              (mkNT nLetDecs,
               choicel [seql [pnt nLetDec; pnt nLetDecs] (bindNT nLetDecs);
                        seql [tokeq SemicolonT; pnt nLetDecs] (bindNT nLetDecs);
                        pegf (empty []) (bindNT nLetDecs)]);
              (mkNT nDecl,
               choicel [
                 seql [tokeq ValT; pnt nPattern; tokeq EqualsT; pnt nE]
                      (bindNT nDecl);
                 seql [tokeq FunT; pnt nAndFDecls] (bindNT nDecl);
                 seql [tokeq ExceptionT; pnt nDconstructor] (bindNT nDecl);
                 seql [pnt nTypeDec] (bindNT nDecl)
               ]);
              (mkNT nDecls,
               choicel [seql [pnt nDecl; pnt nDecls] (bindNT nDecls);
                        seql [tokeq SemicolonT; pnt nDecls] (bindNT nDecls);
                        pegf (empty []) (bindNT nDecls)]);
              (mkNT nSpecLine,
               choicel [seql [tokeq ValT; pnt nV; tokeq ColonT; pnt nType]
                             (bindNT nSpecLine);
                        seql [tokeq TypeT; pnt nTypeName] (bindNT nSpecLine);
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
              (mkNT nStructName, peg_StructName);
              (mkNT nStructure,
               seql [tokeq StructureT; pnt nStructName; pnt nOptionalSignatureAscription;
                     tokeq EqualsT; tokeq StructT; pnt nDecls; tokeq EndT]
                    (bindNT nStructure));
              (mkNT nTopLevelDec,
               pegf (choicel [pnt nStructure; pnt nDecl]) (bindNT nTopLevelDec));
(*            (mkNT nTopLevelDecs,
               rpt (pnt nTopLevelDec)
                   (λtds. [FOLDR
                             (λtd acc.
                                  Nd (mkNT nTopLevelDecs)
                                     (case td of
                                          [] => [acc] (* shouldn't happen *)
                                        | tdh::_ => [tdh; acc]))
                             (Nd (mkNT nTopLevelDecs) []) tds]));
              (mkNT nREPLPhrase,
               choicel [seql [pnt nE; tokeq SemicolonT] (bindNT nREPLPhrase);
                        seql [pnt nTopLevelDecs; tokeq SemicolonT]
                             (bindNT nREPLPhrase)]); *)
              (mkNT nREPLTop,
               choicel [seql [pnt nE; tokeq SemicolonT] (bindNT nREPLTop);
                        seql [pnt nTopLevelDec; tokeq SemicolonT]
                             (bindNT nREPLTop)])
             ] |>
`;

val rules_t = ``cmlPEG.rules``
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
                      [cmlPEG_def, combinTheory.K_DEF,
                       finite_mapTheory.FUPDATE_LIST_THM] rules_t

val _ = print "Calculating application of cmlPEG rules\n"
val cmlpeg_rules_applied = let
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
    save_thm("cmlpeg_rules_applied", LIST_CONJ ths);
    ths
end

val FDOM_cmlPEG = save_thm(
  "FDOM_cmlPEG",
  SIMP_CONV (srw_ss()) [cmlPEG_def,
                        finite_mapTheory.FRANGE_FUPDATE_DOMSUB,
                        finite_mapTheory.DOMSUB_FUPDATE_THM,
                        finite_mapTheory.FUPDATE_LIST_THM]
            ``FDOM cmlPEG.rules``);

val spec0 =
    peg_nt_thm |> Q.GEN `G`  |> Q.ISPEC `cmlPEG`
               |> SIMP_RULE (srw_ss()) [FDOM_cmlPEG]
               |> Q.GEN `n`

val mkNT = ``mkNT``

val cmlPEG_exec_thm = save_thm(
  "cmlPEG_exec_thm",
  TypeBase.constructors_of ``:MMLnonT``
    |> map (fn t => ISPEC (mk_comb(mkNT, t)) spec0)
    |> map (SIMP_RULE bool_ss cmlpeg_rules_applied)
    |> LIST_CONJ)
val _ = computeLib.add_persistent_funs ["cmlPEG_exec_thm"]

val test1 = time EVAL ``peg_exec cmlPEG (pnt nErel) [IntT 3; StarT; IntT 4; SymbolT "/"; IntT (-2); SymbolT ">"; AlphaT "x"] [] done failed``


open lcsymtacs

val frange_image = prove(
  ``FRANGE fm = IMAGE (FAPPLY fm) (FDOM fm)``,
  simp[finite_mapTheory.FRANGE_DEF, pred_setTheory.EXTENSION] >> metis_tac[]);

val peg_range =
    SIMP_CONV (srw_ss())
              (FDOM_cmlPEG :: frange_image :: cmlpeg_rules_applied)
              ``FRANGE cmlPEG.rules``

val peg_start = SIMP_CONV(srw_ss()) [cmlPEG_def]``cmlPEG.start``

val wfpeg_rwts = pegTheory.wfpeg_cases
                   |> ISPEC ``cmlPEG``
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
                  |> ISPEC ``cmlPEG``
                  |> Q.SPEC `pnt n`
                  |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [pnt_def]))

val peg0_rwts = pegTheory.peg0_cases
                  |> ISPEC ``cmlPEG`` |> CONJUNCTS
                  |> map (fn th => map (fn t => Q.SPEC t th)
                                       [`tok P f`, `choice e1 e2 f`, `seq e1 e2 f`,
                                        `tokeq t`, `empty l`, `not e v`])
                  |> List.concat
                  |> map (CONV_RULE
                            (RAND_CONV (SIMP_CONV (srw_ss())
                                                  [tokeq_def])))

val pegfail_t = ``pegfail``
val peg0_rwts = let
  fun filterthis th = let
    val c = concl th
    val (l,r) = dest_eq c
    val (f,_) = strip_comb l
  in
    not (same_const pegfail_t f) orelse is_const r
  end
in
  List.filter filterthis peg0_rwts
end

val pegnt_case_ths = pegTheory.peg0_cases
                      |> ISPEC ``cmlPEG`` |> CONJUNCTS
                      |> map (Q.SPEC `pnt n`)
                      |> map (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [pnt_def])))

fun pegnt(t,acc) = let
  val th =
      prove(``¬peg0 cmlPEG (pnt ^t)``,
            simp(pegnt_case_ths @ cmlpeg_rules_applied @
                 [FDOM_cmlPEG, peg_V_def, peg_UQConstructorName_def,
                  peg_StructName_def,
                  peg_EbaseParen_def,
                  peg_TypeDec_def, choicel_def, seql_def, peg_longV_def,
                  pegf_def, peg_nonfix_def, peg_linfix_def]) >>
            simp(peg0_rwts @ acc))
  val nm = "peg0_" ^ term_to_string t
  val th' = save_thm(nm, SIMP_RULE bool_ss [pnt_def] th)
  val _ = export_rewrites [nm]
in
  th::acc
end

val npeg0_rwts =
    List.foldl pegnt []
               [``nTypeDec``, ``nDecl``, ``nV``, ``nVlist1``, ``nUQTyOp``,
                ``nUQConstructorName``, ``nStructName``, ``nConstructorName``, ``nTypeName``,
                ``nDtypeDecl``, ``nDconstructor``, ``nFDecl``, ``nTyvarN``,
                ``nTyOp``, ``nTbase``, ``nDType``, ``nPType``, ``nType``,
                ``nTypeList1``, ``nTypeList2``,
                ``nRelOps``, ``nPtuple``, ``nPbase``, ``nPapp``, ``nPattern``,
                ``nPatternList``,
                ``nLetDec``, ``nMultOps``, ``nListOps``,
                ``nFQV``, ``nAddOps``, ``nCompOps``, ``nEbase``, ``nEapp``,
                ``nEmult``, ``nEadd``, ``nElistop``, ``nErel``, ``nEcomp``,
                ``nEbefore``,
                ``nEtyped``, ``nElogicAND``, ``nElogicOR``, ``nEhandle``,
                ``nE``, ``nE'``, ``nElist1``,
                ``nSpecLine``, ``nStructure``, ``nTopLevelDec``]

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

fun wfnt(t,acc) = let
  val th =
    prove(``wfpeg cmlPEG (pnt ^t)``,
          SIMP_TAC (srw_ss())
                   (cmlpeg_rules_applied @
                    [wfpeg_pnt, FDOM_cmlPEG, try_def, peg_longV_def,
                     seql_def, peg_TypeDec_def, peg_V_def,
                     peg_EbaseParen_def, peg_StructName_def,
                     peg_UQConstructorName_def, peg_nonfix_def,
                     tokeq_def, peg_linfix_def]) THEN
          simp(wfpeg_rwts @ npeg0_rwts @ peg0_rwts @ acc))
in
  th::acc
end;

val topo_nts = [``nV``, ``nTyvarN``, ``nTypeDec``, ``nDecl``,
                ``nVlist1``, ``nUQTyOp``, ``nUQConstructorName``, ``nStructName``,
                ``nConstructorName``, ``nTyVarList``, ``nTypeName``, ``nTyOp``,
                ``nTbase``, ``nDType``, ``nPType``, ``nListOps``,
                ``nRelOps``, ``nPtuple``, ``nPbase``, ``nPapp``, ``nPattern``,
                ``nPatternList``, ``nPE``,
                ``nPE'``, ``nPEs``, ``nMultOps``, ``nLetDec``, ``nLetDecs``,
                ``nFQV``,
                ``nFDecl``, ``nAddOps``, ``nCompOps``, ``nEbase``, ``nEapp``,
                ``nEmult``, ``nEadd``, ``nElistop``, ``nErel``,
                ``nEcomp``, ``nEbefore``, ``nEtyped``, ``nElogicAND``,
                ``nElogicOR``, ``nEhandle``, ``nE``, ``nE'``,
                ``nType``, ``nTypeList1``, ``nTypeList2``,
                ``nEseq``, ``nElist1``, ``nDtypeDecl``,
                ``nDecls``, ``nDconstructor``, ``nAndFDecls``, ``nSpecLine``,
                ``nSpecLineList``, ``nSignatureValue``,
                ``nOptionalSignatureAscription``, ``nStructure``,
                ``nTopLevelDec``, (* ``nTopLevelDecs``, ``nREPLPhrase``, *)
                ``nREPLTop``]

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

val PEG_exprs = save_thm(
  "PEG_exprs",
  ``Gexprs cmlPEG``
    |> SIMP_CONV (srw_ss())
         [pegTheory.Gexprs_def, pegTheory.subexprs_def,
          subexprs_pnt, peg_start, peg_range, choicel_def, tokeq_def, try_def,
          seql_def, pegf_def, peg_V_def, peg_nonfix_def, peg_EbaseParen_def,
          peg_longV_def, peg_linfix_def, peg_StructName_def,
          peg_TypeDec_def, peg_UQConstructorName_def,
          pred_setTheory.INSERT_UNION_EQ
         ])

val PEG_wellformed = store_thm(
  "PEG_wellformed",
  ``wfG cmlPEG``,
  simp[pegTheory.wfG_def, pegTheory.Gexprs_def, pegTheory.subexprs_def,
       subexprs_pnt, peg_start, peg_range, DISJ_IMP_THM, FORALL_AND_THM,
       choicel_def, seql_def, pegf_def, tokeq_def, try_def,
       peg_linfix_def, peg_UQConstructorName_def, peg_TypeDec_def,
       peg_V_def, peg_EbaseParen_def, peg_nonfix_def,
       peg_longV_def, peg_StructName_def] >>
  simp(cml_wfpeg_thm :: wfpeg_rwts @ peg0_rwts @ npeg0_rwts));
val _ = export_rewrites ["PEG_wellformed"]

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

local
  val c = concl FDOM_cmlPEG
  val r = rhs c
  fun recurse acc t =
      case Lib.total pred_setSyntax.dest_insert t of
          SOME(e,t') => recurse (e :: acc) t'
        | NONE => acc
  val nts = recurse [] r
in
val FDOM_cmlPEG_nts = let
  fun p t = prove(``^t ∈ FDOM cmlPEG.rules``, simp[FDOM_cmlPEG])
in
  save_thm("FDOM_cmlPEG_nts", LIST_CONJ (map p nts)) before
  export_rewrites ["FDOM_cmlPEG_nts"]
end
val NTS_in_PEG_exprs = let
  val exprs_th' = REWRITE_RULE [pnt_def] PEG_exprs
  val exprs_t = rhs (concl exprs_th')
  fun p t = let
    val _ = print ("PEGexpr: "^term_to_string t^"\n")
    val th0 = prove(``nt ^t I ∈ ^exprs_t``, simp[pnt_def])
              handle e => (print("Failed on "^term_to_string t^"\n");
                           raise e)
  in
    CONV_RULE (RAND_CONV (K (SYM exprs_th'))) th0
  end
  val th = LIST_CONJ (map p nts)
in
  save_thm("NTS_in_PEG_exprs", th) before export_rewrites ["NTS_in_PEG_exprs"]
end

end (* local *)


val _ = export_theory()
