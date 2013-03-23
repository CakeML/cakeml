open HolKernel Parse boolLib bossLib

open mmlGrammarTheory pegexecTheory

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

(* ----------------------------------------------------------------------
    PEG for types
   ---------------------------------------------------------------------- *)

val peg_Type_def = Define`
  peg_Type = seq (nt (mkNT nDType) I)
                 (choice (seq (tokeq ArrowT)
                              (nt (mkNT nType) I)
                              (++))
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
           (rpt (nt (mkNT nTyOp) I) FLAT)
           (λa ops. FOLDL (λacc opn. [Nd (mkNT nDType) (acc ++ [opn])])
                          a ops))
      (choice
        (seq (nt (mkNT nTyOp) (λx. [Nd (mkNT nDType) x]))
             (rpt (nt (mkNT nTyOp) I) FLAT)
             (λa ops. FOLDL (λacc opn. [Nd (mkNT nDType) (acc ++ [opn])])
                            a ops))
        (seq (tokeq LparT)
             (seq (nt (mkNT nType) I)
                  (choice
                     (* ")" TyOp* *)
                     (seq (tokeq RparT)
                          (rpt (nt (mkNT nTyOp) I) FLAT)
                          (++))
                     (* ("," Type)* ")" TyOp TyOp* *)
                     (seq (rpt (seq (tokeq CommaT)
                                    (nt (mkNT nType) I)
                                    (++))
                               FLAT)
                          (seq (tokeq RparT)
                               (seq (nt (mkNT nTyOp) I)
                                    (rpt (nt (mkNT nTyOp) I) FLAT)
                                    (++))
                               (++))
                          (++))
                     sumID)
                  calcTyOp)
             (λa b. b))
        sumID)
      sumID
`;

val peg_StarTypes_def = Define`
  peg_StarTypes = peg_linfix (mkNT nStarTypes)
                             (nt (mkNT nDType) I)
                             (tokeq StarT)
`;

val peg_StarTypesP_def = Define`
  peg_StarTypesP =
    choice (seq (tokeq LparT)
                (seq (nt (mkNT nStarTypes) I) (tokeq RparT) (++))
                (++))
           (nt (mkNT nStarTypes) I)
           (bindNT nStarTypesP o sumID)
`;

val peg_TypeName_def = Define`
  peg_TypeName =
    choice (nt (mkNT nTyOp) I)
           (choice
              (seq (tokeq LparT)
                   (seq (peg_linfix (mkNT nTyVarList)
                                    (tok isTyvarT mktokLf)
                                    (tokeq CommaT))
                        (seq (tokeq RparT) (nt (mkNT nTyOp) I) (++))
                        (++))
                   (++))
              (seq (tok isTyvarT mktokLf) (nt (mkNT nTyOp) I) (++))
              sumID)
           (bindNT nTypeName o sumID)
`;

val peg_ConstructorName_def = Define`
  peg_ConstructorName =
    tok (λt. do s <- destAlphaT t ;
                assert (s ≠ "" ∧ isUpper (HD s) ∨ s ∈ {"true"; "false"})
             od = SOME ())
        (bindNT nConstructorName o mktokLf)
`;

(* Dconstructor ::= ConstructorName "of" StarTypesP | ConstructorName; *)
val peg_Dconstructor_def = Define`
  peg_Dconstructor =
    seq (nt (mkNT nConstructorName) I)
        (choice (seq (tokeq OfT) (nt (mkNT nStarTypesP) I) (++))
                (empty [])
                sumID)
        (λl1 l2. bindNT nDconstructor (l1 ++ l2))
`;


(* DtypeDecl ::= TypeName "=" DtypeCons ; *)
val peg_DtypeDecl_def = Define`
  peg_DtypeDecl =
    seq (nt (mkNT nTypeName) I)
        (seq (tokeq EqualsT)
             (*  DtypeCons ::= Dconstructor | DtypeCons "|" Dconstructor; *)
             (peg_linfix (mkNT nDtypeCons) (nt (mkNT nDconstructor) I)
                         (tokeq BarT))
             (++))
        (λl1 l2. bindNT nDtypeDecl (l1 ++ l2))
`;

val peg_TypeDec_def = Define`
  peg_TypeDec =
    seq (tokeq DatatypeT)
        (peg_linfix (mkNT nDtypeDecls) (nt (mkNT nDtypeDecl) I)
                    (tokeq AndT))
        (λl1 l2. [Nd (mkNT nTypeDec) (l1 ++ l2)])
`;

(* expressions *)
val peg_V_def = Define`
  peg_V =
   choice (tok (λt.
                  do s <- destAlphaT t;
                     assert(s ∉ {"before"; "div"; "mod"; "o"; "true"; "false"} ∧                            s ≠ "" ∧ ¬isUpper (HD s))
                  od = SOME ())
               mktokLf)
          (tok (λt.
                  do s <- destSymbolT t;
                     assert(s ∉ {"+"; "-"; "/"; "<"; ">"; "<="; ">="; "<>"})
                  od = SOME ())
               mktokLf)
          (bindNT nV o sumID)
`

val peg_multops_def = Define`
  peg_multops = pegf (choicel (MAP tokeq
                                   [StarT; SymbolT "/"; AlphaT "mod";
                                    AlphaT "div"]))
                     (bindNT nMultOps)
`;

val peg_addops_def = Define`
  peg_addops = pegf (choicel [tokeq (SymbolT "+"); tokeq (SymbolT "-")])
                    (bindNT nAddOps)
`;

val peg_relops_def = Define`
  peg_relops = pegf (choicel (tok ((=) EqualsT) mktokLf ::
                              MAP (tokeq o SymbolT)
                                  ["<"; ">"; "<="; ">="; "<>"]))
                    (bindNT nRelOps)
`;

val peg_Ebase_def = Define`
  peg_Ebase =
    choicel [tok isInt (bindNT nEbase o mktokLf);
             nt (mkNT nV) (bindNT nEbase);
             nt (mkNT nConstructorName) (bindNT nEbase);
             seql [tokeq LparT; nt (mkNT nE) I; tokeq RparT]
                  (bindNT nEbase);
             seql [tokeq LetT;
                   choicel [seql [tokeq ValT; nt (mkNT nV) I; tokeq EqualsT;
                                  nt (mkNT nE) I; tokeq InT; nt (mkNT nE) I;
                                  tokeq EndT] I;
                            seql [tokeq FunT; nt (mkNT nAndFDecls) I;
                                  tokeq InT; nt (mkNT nE) I; tokeq EndT] I]]
                  (bindNT nEbase)
            ]
`;

val peg_Eapp_def = Define`
  peg_Eapp =
    choice (seql [nt (mkNT nConstructorName) I; nt (mkNT nEtuple) I]
                 (bindNT nEapp))
           (seq (nt (mkNT nEbase) I)
                (rpt (nt (mkNT nEbase) I) FLAT)
                (λa b. [FOLDL (λa b. Nd (mkNT nEapp) [a; b])
                              (Nd (mkNT nEapp) [HD a])
                              b]))
           sumID
`;

val mmlPEG_def = zDefine`
  mmlPEG = <|
    start := nt (mkNT nDecl) I;
    rules := FEMPTY |++
             [(mkNT nV, peg_V);
              (mkNT nEapp, peg_Eapp);
              (mkNT nEtuple,
               seql [tokeq LparT; nt (mkNT nElist2) I; tokeq RparT]
                    (bindNT nEtuple));
              (mkNT nElist2,
               seql [nt (mkNT nE) I; tokeq CommaT; nt (mkNT nElist1) I]
                    (bindNT nElist2));
              (mkNT nElist1,
               peg_linfix (mkNT nElist1) (nt (mkNT nE) I) (tokeq CommaT));
              (mkNT nMultOps, peg_multops);
              (mkNT nAddOps, peg_addops);
              (mkNT nRelOps, peg_relops);
              (mkNT nEbase, peg_Ebase);
              (mkNT nEmult, peg_linfix (mkNT nEmult)
                                       (nt (mkNT nEapp) I)
                                       (nt (mkNT nMultOps) I));
              (mkNT nEadd, peg_linfix (mkNT nEadd) (nt (mkNT nEmult) I)
                                      (nt (mkNT nAddOps) I));
              (mkNT nErel, peg_nonfix nErel (nt (mkNT nEadd) I)
                                      (nt (mkNT nRelOps) I));
              (mkNT nEcomp, peg_linfix (mkNT nEcomp) (nt (mkNT nErel) I)
                                       (tokeq (AlphaT "o")));
              (mkNT nEbefore, peg_linfix (mkNT nEbefore) (nt (mkNT nEcomp) I)
                                         (tokeq (AlphaT "before")));
              (mkNT nEtyped, seql [nt (mkNT nEbefore) I;
                                   try (seql [tokeq ColonT;
                                              nt (mkNT nType) I] I)]
                                  (bindNT nEtyped));
              (mkNT nElogicAND,
               peg_linfix (mkNT nElogicAND) (nt (mkNT nEtyped) I)
                          (tokeq AndalsoT));
              (mkNT nElogicOR,
               peg_linfix (mkNT nElogicOR) (nt (mkNT nElogicAND) I)
                          (tokeq OrelseT));
              (mkNT nE,
               choicel [seql [tokeq RaiseT; nt (mkNT nE) I] (bindNT nE);
                        nt (mkNT nElogicOR) (bindNT nE);
                        seql [tokeq IfT; nt (mkNT nE) I; tokeq ThenT;
                              nt (mkNT nE) I; tokeq ElseT; nt(mkNT nE) I]
                             (bindNT nE)]);
              (mkNT nType, peg_Type);
              (mkNT nDType, peg_DType);
              (mkNT nTyOp, peg_TyOp);
              (mkNT nStarTypes, peg_StarTypes);
              (mkNT nStarTypesP, peg_StarTypesP);
              (mkNT nTypeName, peg_TypeName);
              (mkNT nTypeDec, peg_TypeDec);
              (mkNT nDtypeDecl, peg_DtypeDecl);
              (mkNT nDconstructor, peg_Dconstructor);
              (mkNT nConstructorName, peg_ConstructorName)
             ] |>
`;

val rules = SIMP_CONV (srw_ss()) [mmlPEG_def] ``mmlPEG.rules``
val spec0 =
    peg_nt_thm |> Q.GEN `G`  |> Q.ISPEC `mmlPEG`
               |> SIMP_RULE (srw_ss()) [rules, finite_mapTheory.FUPDATE_LIST]
               |> Q.GEN `n`

val mkNT = ``mkNT``

val mmlPEG_exec_thm = save_thm(
  "mmlPEG_exec_thm",
  TypeBase.constructors_of ``:MMLnonT``
    |> map (fn t => ISPEC (mk_comb(mkNT, t)) spec0)
    |> map (SIMP_RULE (srw_ss()) [finite_mapTheory.FAPPLY_FUPDATE_THM])
    |> LIST_CONJ)
val _ = computeLib.add_persistent_funs ["mmlPEG_exec_thm"]

val test1 = time EVAL ``peg_exec mmlPEG (nt (mkNT nErel) I) [IntT 3; StarT; IntT 4; SymbolT "/"; IntT (-2); SymbolT ">"; AlphaT "x"] [] done failed``


val _ = export_theory()
