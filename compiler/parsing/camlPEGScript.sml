(*
  Definition of a PEG for (a subset of) OCaml.
 *)

open preamble caml_lexTheory;
open pegexecTheory pegTheory;
open finite_mapSyntax;

val _ = new_theory "camlPEG";

val _ = enable_monadsyntax ();

val _ = enable_monad "option";

(* Some definitions taken from cmlPEG:
 *)

Definition sumID_def:
  sumID (INL x) = x ∧
  sumID (INR y) = y
End

Definition mktokLf_def:
  mktokLf t = [Lf (TOK (FST t), SND t)]
End

Definition mkNd_def:
  mkNd ntnm l = Nd (ntnm, ptree_list_loc l) l
End

Definition bindNT0_def:
  bindNT0 ntnm l = Nd (INL ntnm, ptree_list_loc l) l
End

Definition bindNT_def:
  bindNT ntnm l = [bindNT0 ntnm l]
End

Definition mk_linfix_def:
  mk_linfix tgt acc [] = acc ∧
  mk_linfix tgt acc [t] = acc ∧
  mk_linfix tgt acc (opt::t::rest) =
    mk_linfix tgt (mkNd tgt [acc; opt; t]) rest
End

(* TODO: unused *)
Definition mk_rinfix_def:
  mk_rinfix tgt [] = mkNd tgt [] ∧
  mk_rinfix tgt [t] = mkNd tgt [t] ∧
  mk_rinfix tgt (t::opt::rest) = mkNd tgt [t; opt; mk_rinfix tgt rest]
End

Definition peg_linfix_def:
  peg_linfix tgtnt rptsym opsym =
    seq rptsym (rpt (seq opsym rptsym (++)) FLAT)
        (λa b. case a of
                   [] => []
                  | h::_ => [mk_linfix tgtnt (mkNd tgtnt [h]) b])
End

Definition choicel_def:
  choicel [] = not (empty []) [] ∧
  choicel (h::t) = choice h (choicel t) sumID
End

Definition pegf_def:
  pegf sym f = seq sym (empty []) (λl1 l2. f l1)
End

Definition seql_def:
  seql l f = pegf (FOLDR (\p acc. seq p acc (++)) (empty []) l) f
End

Definition try_def:
  try sym = choicel [sym; empty []]
End

Definition tokeq_def:
  tokeq t = tok ((=) t) mktokLf
End

Definition tokSymP_def:
  tokSymP P =
    tok (λt. (do s <- destSymbol t; assert (P s) od) = SOME ()) mktokLf
End

Definition tokIdP_def:
  tokIdP P =
    tok (λt. (do s <- destIdent t; assert (P s) od) = SOME ()) mktokLf
End

Definition pnt_def:
  pnt ntsym = nt (INL ntsym) I
End

(* -------------------------------------------------------------------------
 * Non-terminals
 * ------------------------------------------------------------------------- *)

Definition validCoreOpChar_def:
  validCoreOpChar c = MEM c "$&*+-/=>@^|"
End

Definition validOpChar_def:
  validOpChar c ⇔ MEM c "!?%<:." ∨ validCoreOpChar c
End

Definition validPrefixSym_def:
  validPrefixSym s =
    case s of
      [] => F
    | c::cs =>
        (c = #"!" ∨ (c = #"?" ∨ c = #"~" ∧ cs ≠ "")) ∧
        EVERY validOpChar cs
End

Definition validInfixSym_def:
  validInfixSym s =
    case s of
      [] => F
    | c::cs =>
      ((validCoreOpChar c ∨ c = #"%" ∨ c = #"<") ∨
       (c = #"#" ∧ cs ≠ "")) ∧
      EVERY validOpChar cs
End

Definition validMultOp_def:
  validMultOp s =
    case s of
      [] => F
    | c::cs =>
        (MEM c "*%/" ∧ cs ≠ "" ∧ EVERY validOpChar cs) ∨
        MEM s [ "%"; "/" ]
End

Definition validRelOp_def:
  validRelOp s =
    case s of
      [] => F
    | c::cs =>
        MEM c "<>|&$" ∧ cs ≠ "" ∧ EVERY validOpChar cs
End

Definition validAddOp_def:
  validAddOp s =
    case s of
      [] => F
    | c::cs => MEM c "+-" ∧ cs ≠ "" ∧ EVERY validOpChar cs
End

Definition validRelOp_def:
  validRelOp s =
    case s of
      [] => F
    | c::cs => MEM c "=<>|&$" ∧ cs ≠ "" ∧ EVERY validOpChar cs
End

Definition validShiftOp_def:
  validShiftOp s =
    case s of
      c::d::cs => c = #"*" ∧ d = #"*" ∧ EVERY validOpChar cs
    | _ => F
End

Definition validCatOp_def:
  validCatOp s =
    case s of
      [] => F
    | c::cs => (c = #"@" ∨ c = CHR 94) ∧ EVERY validOpChar cs
End

Definition idChar_def:
  idChar P = EVERY (λc. P c ∨ c = #"_" ∨ c = #"'" ∨ isDigit c)
End

Definition validConsId_def:
  validConsId s =
    case s of
      [] => F
    | c::cs => isUpper c ∧ idChar isLower cs
End

Definition validFunId_def:
  validFunId s =
    case s of
      [] => F
    | c::cs => (isLower c ∨ c = #"_") ∧ idChar isLower cs
End

Datatype:
  camlNT =
    (* expressions *)
      nLiteral | nIdent | nEBase | nEList
    | nEApp | nEConstr | nEFunapp | nETagapp | nEAssert | nELazy
    | nEPrefix | nENeg | nEShift | nEMult
    | nEAdd | nECons | nECat | nERel
    | nEAnd | nEOr | nEProd | nEIf | nESeq
    | nEMatch | nETry | nEFun | nEFunction | nELet | nELetExn
    | nEWhile | nEFor | nExpr
    (* pattern matches *)
    | nParameter | nParameters | nLetBinding | nLetBindings
    | nPatternMatch | nPatternMatches
    (* type definitions *)
    | nTypeDefinition | nTypeDef | nTypeInfo | nTypeRepr | nTypeReprs
    | nConstrDecl | nConstrArgs | nExcDefinition
    (* patterns *)
    | nPAny | nPBase | nPLazy | nPConstr | nPTagapp | nPApp | nPCons | nPProd
    | nPOr | nPAs | nPList | nPattern
    (* types *)
    | nTVar | nTAny | nTBase | nTConstr | nTApp | nTProd | nTFun | nTAs | nType
    (* definitions *)
    | nDefinition | nTopLet | nModuleItem | nModuleItems
    (* misc *)
    | nShiftOp | nMultOp | nAddOp | nRelOp | nAndOp | nOrOp
    | nStart
End

(*
   TODO
   The following is a (possibly incomplete) list of missing things:
   - Expression rules for the following things are missing:
     + Assignments, i.e. <- :=
   - The module syntax (all module expressions and the module types), and some
     top-levle definitions such as 'open'.

   Also the following is broken:
   - Somehow I forgot to allow identifiers to contain dots
     (i.e. module paths); this needs to be fixed also in the
     lexer.
   - I've assigned a bunch of closed expressions (e.g. while, for) to the
     lowest fixity, but it's possible they should go elsewhere.
   - [1;2;3] should parse into a list of three elements but I think it's
     currently parsed into the sequence (seq 1 (seq 2 3)) of expressions.
 *)

Definition camlPEG_def[nocompute]:
  camlPEG = <|
    anyEOF   := "Unexpected end-of-file";
    tokFALSE := "Unexpected token";
    tokEOF   := "Expected token, found end-of-file";
    notFAIL  := "Not combinator failed";
    start := pnt nStart;
    rules := FEMPTY |++ [
      (* -- Definitions ---------------------------------------------------- *)
      (INL nModuleItem,
       seql [try (tokeq SemisT); choicel [pnt nDefinition; pnt nExpr]]
            (bindNT nModuleItem));
      (INL nModuleItems,
       seql [rpt (pnt nModuleItem) FLAT; try (tokeq SemisT)]
            (bindNT nModuleItems));
      (INL nTopLet,
       seql [tokeq LetT; try (tokeq RecT); pnt nLetBindings]
            (bindNT nTopLet));
      (INL nDefinition,
       pegf (choicel [pnt nTopLet;
                      pnt nTypeDefinition;
                      pnt nExcDefinition;
                      (* module definition *)
                      (* module type *)
                      (* open modulename *)
                      (* include moduleexpr *)
                      ])
            (bindNT nDefinition));
      (* -- Typedef -------------------------------------------------------- *)
      (INL nExcDefinition,
       seql [tokeq ExceptionT;
             choicel [pnt nConstrDecl;
                      seql [tokIdP validConsId; tokeq EqualT;
                            tokIdP validConsId] I]]
            (bindNT nExcDefinition));
      (INL nTypeDefinition,
       seql [tokeq TypeT; try (tokeq NonrecT); pnt nTypeDef;
             rpt (seql [tokeq AndT; pnt nTypeDef] I) FLAT]
            (bindNT nTypeDefinition));
      (INL nTypeDef,
       seql [choicel [seql [tokeq LparT; pnt nTVar;
                            rpt (seql [tokeq CommaT; pnt nTVar] I) FLAT;
                            tokeq RparT] I;
                      pnt nTVar;
                      empty []];
             tokIdP validFunId; pnt nTypeInfo]
            (bindNT nTypeDef));
      (INL nTypeInfo,
       seql [try (seql [tokeq EqualT; pnt nType] I);
             try (pnt nTypeRepr)]
            (bindNT nTypeInfo));
      (INL nTypeRepr,
       seql [try (tokeq BarT); pnt nConstrDecl; try (pnt nTypeReprs)]
            (bindNT nTypeRepr));
      (INL nTypeReprs,
       seql [tokeq BarT; pnt nConstrDecl; try (pnt nTypeReprs)]
            (bindNT nTypeReprs));
      (INL nConstrDecl,
       seql [choicel [tokIdP validConsId;
                      tokSymP (λs. s = "[]");
                      seql [tokeq LparT; tokeq ColonsT; tokeq RparT] I];
             try (seql [tokeq OfT; pnt nConstrArgs] I)]
            (bindNT nConstrDecl));
      (INL nConstrArgs,
       seql [pnt nType; rpt (seql [tokeq StarT; pnt nType] I) FLAT]
            (bindNT nConstrArgs));
      (* -- Type5 ---------------------------------------------------------- *)
      (INL nTVar,
       seql [tokeq TickT; pnt nIdent] (bindNT nTVar));
      (INL nTAny,
       pegf (tokeq AnyT) (bindNT nTAny));
      (INL nTBase,
       pegf (choicel [pnt nTVar;
                      pnt nTAny;
                      seql [tokeq LparT; pnt nType; tokeq RparT] I;
                      pnt nTConstr])
            (bindNT nTBase));
      (* -- Type4 ---------------------------------------------------------- *)
      (INL nTConstr,
       seql [choicel [seql [tokeq LparT; pnt nType;
                            rpt (seql [tokeq CommaT; pnt nType] I) FLAT;
                            tokeq RparT] I;
                      pnt nType;
                      empty []];
             tokIdP validConsId]
            (bindNT nTConstr));
      (INL nTApp,
       pegf (choicel [pnt nTConstr; pnt nTBase])
            (bindNT nTApp));
      (* -- Type3 ---------------------------------------------------------- *)
      (INL nTProd,
       seql [pnt nTApp; try (seql [tokeq StarT; pnt nTProd] I)]
            (bindNT nTProd));
      (* -- Type2 ---------------------------------------------------------- *)
      (INL nTFun,
       seql [pnt nTProd; try (seql [tokeq RarrowT; pnt nTFun] I)]
            (bindNT nTFun));
      (* -- Type1 ---------------------------------------------------------- *)
      (INL nTAs,
       seql [pnt nTFun; tokeq AsT; tokeq TickT; pnt nIdent]
            (bindNT nTAs));
      (* -- Type ----------------------------------------------------------- *)
      (INL nType,
       pegf (pnt nTAs) (bindNT nType));
      (* -- Expr16 --------------------------------------------------------- *)
      (INL nEList,
       seql [tokeq LbrackT;
             pnt nExpr;
             rpt (seql [tokeq SemiT; pnt nExpr] I) FLAT;
             try (tokeq SemiT);
             tokeq RbrackT]
            (bindNT nEList));
      (INL nLiteral,
       choicel [
         tok isInt    (bindNT nLiteral o mktokLf);
         tok isString (bindNT nLiteral o mktokLf);
         tok isChar   (bindNT nLiteral o mktokLf);
         tok (λx. MEM x [TrueT; FalseT]) (bindNT nLiteral o mktokLf);
         pegf (pnt nEList) (bindNT nLiteral)]);
      (INL nIdent,
       tok isIdent (bindNT nIdent o mktokLf));
      (INL nEBase,
       choicel [
         pegf (pnt nLiteral) (bindNT nEBase);
         pegf (pnt nIdent) (bindNT nEBase);
         seql [tokeq LparT; pnt nExpr;
               try (seql [tokeq ColonT; pnt nType] I);
               tokeq RparT] (bindNT nEBase);
         seql [tokeq BeginT; pnt nExpr; tokeq EndT] (bindNT nEBase)
       ]);
      (* -- Expr15 --------------------------------------------------------- *)
      (INL nEAssert,
       seql [tokeq AssertT; pnt nEBase] (bindNT nEAssert));
      (INL nELazy,
       seql [tokeq LazyT; pnt nEBase] (bindNT nELazy));
      (INL nEConstr,
       seql [tokIdP validConsId; pnt nEBase] (bindNT nEConstr));
      (INL nEFunapp,
       seql [tokIdP validFunId; pnt nEBase] (bindNT nEFunapp));
      (INL nETagapp,
       seql [tokeq BtickT; tokIdP validFunId; pnt nEBase]
            (bindNT nETagapp));
      (INL nEApp,
       pegf (choicel (MAP pnt [nELazy; nEAssert; nEConstr; nEFunapp;
                               nETagapp; nEBase]))
            (bindNT nEApp));
      (* -- Expr14 --------------------------------------------------------- *)
      (INL nEPrefix,
       seql [try (tokSymP validPrefixSym); pnt nEApp] (bindNT nEPrefix));
      (* -- Expr13 --------------------------------------------------------- *)
      (INL nENeg,
       seql [try (choicel [tokeq MinusT; tokeq MinusFT]); pnt nEPrefix]
            (bindNT nENeg));
      (* -- Expr12 --------------------------------------------------------- *)
      (INL nShiftOp,
       pegf (choicel [tokSymP validShiftOp; tokeq LslT; tokeq LsrT; tokeq AsrT])
            (bindNT nShiftOp));
      (INL nEShift,
       seql [pnt nENeg; try (seql [pnt nShiftOp; pnt nEShift] I)]
            (bindNT nEShift));
      (* -- Expr11 --------------------------------------------------------- *)
      (INL nMultOp,
       pegf (choicel [tokeq StarT; tokeq ModT; tokeq LandT; tokeq LorT;
                      tokeq LxorT; tokSymP validMultOp])
            (bindNT nMultOp));
      (INL nEMult,
       peg_linfix (INL nEMult) (pnt nEShift) (pnt nMultOp));
      (* -- Expr10 --------------------------------------------------------- *)
      (INL nAddOp,
       pegf (choicel [tokeq PlusT; tokeq MinusT; tokSymP validAddOp])
            (bindNT nAddOp));
      (INL nEAdd,
       peg_linfix (INL nEAdd) (pnt nEMult) (pnt nAddOp));
      (* -- Expr9 ---------------------------------------------------------- *)
      (INL nECons,
       seql [pnt nEAdd; try (seql [tokeq ColonsT; pnt nECons] I)]
            (bindNT nECons));
      (* -- Expr8 ---------------------------------------------------------- *)
      (INL nECat,
       seql [pnt nECons; try (seql [tokSymP validCatOp; pnt nECat] I)]
            (bindNT nECat));
      (* -- Expr7 ---------------------------------------------------------- *)
      (INL nRelOp,
       pegf (choicel [tokeq EqualT; tokeq LessT; tokeq GreaterT; tokeq NeqT;
                      tokSymP validRelOp])
            (bindNT nRelOp));
      (INL nERel,
       peg_linfix (INL nERel) (pnt nECat) (pnt nRelOp));
      (* -- Expr6 ---------------------------------------------------------- *)
      (INL nAndOp,
       pegf (choicel [tokeq AmpT; tokeq AndalsoT])
            (bindNT nAndOp));
      (INL nEAnd,
       seql [pnt nERel; try (seql [pnt nAndOp; pnt nEAnd] I)]
            (bindNT nEAnd));
      (* -- Expr5 ---------------------------------------------------------- *)
      (INL nOrOp,
       pegf (choicel [tokeq OrelseT; tokeq OrT])
            (bindNT nOrOp));
      (INL nEOr,
       seql [pnt nEAnd; try (seql [pnt nOrOp; pnt nEOr] I)]
            (bindNT nEOr));
      (* -- Expr4 ---------------------------------------------------------- *)
      (INL nEProd,
       seql [pnt nEOr; try (seql [tokeq CommaT; pnt nEProd] I)]
            (bindNT nEProd));
      (* -- Expr3: assignments --------------------------------------------- *)
      (* -- Expr2 ---------------------------------------------------------- *)
      (INL nEIf,
       pegf (choicel [seql [tokeq IfT; pnt nExpr; tokeq ThenT; pnt nExpr;
                            try (seql [tokeq ElseT; pnt nExpr] I)] I;
                      pnt nEProd])
            (bindNT nEIf));
      (* -- Expr1 ---------------------------------------------------------- *)
      (INL nESeq,
       pegf (choicel [seql [pnt nEIf; try (seql [tokeq SemiT; pnt nESeq] I)] I;
                      pnt nEIf])
            (bindNT nESeq));
      (* -- Expr0 ---------------------------------------------------------- *)
      (INL nELet,
       seql [tokeq LetT; try (tokeq RecT); pnt nLetBindings;
             tokeq InT; pnt nExpr]
            (bindNT nELet));
      (INL nELetExn,
       seql [tokeq LetT; tokeq ExceptionT; pnt nConstrDecl; tokeq InT;
             pnt nExpr]
            (bindNT nELetExn));
      (INL nEMatch,
       seql [tokeq MatchT; pnt nExpr; tokeq WithT; pnt nPatternMatch]
            (bindNT nEMatch));
      (INL nEFun,
       seql [tokeq FunT; pnt nParameters;
             try (seql [tokeq ColonT; pnt nType] I);
             tokeq RarrowT; pnt nExpr]
            (bindNT nEFun));
      (INL nEFunction,
       seql [tokeq FunctionT; pnt nPatternMatch]
            (bindNT nEFunction));
      (INL nETry,
       seql [tokeq TryT; pnt nExpr; tokeq WithT; pnt nPatternMatch]
            (bindNT nETry));
      (* -- Expr: everything else  ----------------------------------------- *)
      (INL nEWhile,
       seql [tokeq WhileT; pnt nExpr; tokeq DoT; pnt nExpr; tokeq DoneT]
            (bindNT nEWhile));
      (INL nEFor,
       seql [tokeq ForT; pnt nIdent; tokeq EqualT;
             choicel [tokeq ToT; tokeq DowntoT]; pnt nExpr;
             tokeq DoT; pnt nExpr; tokeq DoneT]
            (bindNT nEFor));
      (INL nExpr,
       pegf (choicel [
               (* e1: *)
               pnt nESeq;
               (* e0: *)
               pnt nELet; pnt nELetExn; pnt nEMatch; pnt nEFun; pnt nEFunction;
               pnt nETry;
               (* everything else: *)
               pnt nEWhile; pnt nEFor])
            (bindNT nExpr));
      (* -- Pattern matches etc. ------------------------------------------- *)
      (INL nPatternMatch,
       seql [try (tokeq BarT); pnt nPattern;
             try (seql [tokeq WhenT; pnt nExpr] I); tokeq RarrowT; pnt nExpr;
             try (pnt nPatternMatches)]
            (bindNT nPatternMatch));
      (INL nPatternMatches,
       seql [tokeq BarT; pnt nPattern;
             try (seql [tokeq WhenT; pnt nExpr] I); tokeq RarrowT; pnt nExpr;
             try (pnt nPatternMatches)]
            (bindNT nPatternMatches));
      (INL nLetBindings,
       seql [pnt nLetBinding; try (seql [tokeq AndT; pnt nLetBindings] I)]
            (bindNT nLetBindings));
      (INL nLetBinding,
       pegf (choicel [seql [pnt nPattern; tokeq EqualT; pnt nExpr] I;
                      seql [pnt nIdent; try (pnt nParameters);
                            try (seql [tokeq ColonT; pnt nType] I);
                            tokeq EqualT; pnt nExpr ] I])
            (bindNT nLetBinding));
      (INL nParameters,
       seql [pnt nParameter; try (pnt nParameters)]
            (bindNT nParameters));
      (INL nParameter, (* only one type of parameter supported; collapse? *)
       pegf (pnt nPattern) (bindNT nParameter));
      (* -- Pat8 ----------------------------------------------------------- *)
      (INL nPList,
       seql [tokeq LbrackT;
             pnt nPattern;
             rpt (seql [tokeq SemiT; pnt nPattern] I) FLAT;
             try (tokeq SemiT);
             tokeq RbrackT]
            (bindNT nPList));
      (INL nPAny,
       pegf (tokeq AnyT) (bindNT nPAny));
      (INL nPBase,
       pegf (choicel [pnt nIdent;
                      pnt nPAny;
                      pnt nPList;
                      seql [tokeq LparT; pnt nPattern;
                            try (seql [tokeq ColonT; pnt nType] I);
                            tokeq RparT] I;
                      seql [tok isChar (bindNT nLiteral o mktokLf);
                            tokeq DotsT;
                            tok isChar (bindNT nLiteral o mktokLf)] I])
            (bindNT nPBase));
      (* -- Pat7 ----------------------------------------------------------- *)
      (INL nPLazy,
       seql [tokeq LazyT; pnt nPBase]
            (bindNT nPLazy));
      (* -- Pat6 ----------------------------------------------------------- *)
      (INL nPConstr,
       seql [tokIdP validConsId; pnt nPLazy] (bindNT nPConstr));
      (INL nPTagapp,
       seql [tokeq TickT; tokIdP validFunId; pnt nPLazy] (bindNT nPTagapp));
      (INL nPApp,
       pegf (choicel [pnt nPConstr; pnt nPTagapp; pnt nPLazy])
            (bindNT nPApp));
      (* -- Pat5 ----------------------------------------------------------- *)
      (INL nPCons,
       seql [pnt nPApp; try (seql [tokeq ColonsT; pnt nPCons] I)]
            (bindNT nPCons));
      (* -- Pat4 ----------------------------------------------------------- *)
      (INL nPProd,
       seql [pnt nPCons; try (seql [tokeq CommaT; pnt nPProd] I)]
            (bindNT nPProd));
      (* -- Pat3 ----------------------------------------------------------- *)
      (INL nPOr,
       peg_linfix (INL nPOr) (pnt nPProd) (tokeq BarT));
      (* -- Pat2 ----------------------------------------------------------- *)
      (INL nPAs,
       seql [pnt nPOr; tokeq AsT; pnt nIdent]
            (bindNT nPAs));
      (* -- Pat1 ----------------------------------------------------------- *)
      (INL nPattern,
       pegf (pnt nPAs) (bindNT nPattern));
      (INL nStart,
       seql [try (pnt nModuleItems); not (any (K [])) [] ] (bindNT nStart))
      ] |>
End

(* -------------------------------------------------------------------------
 * All of the stuff below is taken from cmlPEGScript. Its for doing EVAL
 * using peg_exec:
 * ------------------------------------------------------------------------- *)

val rules_t = “camlPEG.rules”;
fun ty2frag ty = let
  open simpLib
  val {convs,rewrs} = TypeBase.simpls_of ty
in
  merge_ss (rewrites rewrs :: map conv_ss convs)
end

val rules = SIMP_CONV (bool_ss ++ ty2frag ``:(α,β,γ,δ)peg``)
                      [camlPEG_def, combinTheory.K_DEF,
                       finite_mapTheory.FUPDATE_LIST_THM] rules_t

val _ = print "Calculating application of camlPEG rules\n"
val camlpeg_rules_applied = let
  val app0 = finite_mapSyntax.fapply_t
  val theta =
      Type.match_type (type_of app0 |> dom_rng |> #1) (type_of rules_t)
  val app = inst theta app0
  val app_rules = AP_TERM app rules
  val sset = bool_ss ++ ty2frag ``:'a + 'b`` ++ ty2frag ``:token``
  fun mkrule t =
      AP_THM app_rules (sumSyntax.mk_inl (t, “:num”))
      |> SIMP_RULE sset [finite_mapTheory.FAPPLY_FUPDATE_THM]
  val ths = TypeBase.constructors_of ``:camlNT`` |> map mkrule
in
    save_thm("camlpeg_rules_applied", LIST_CONJ ths);
    ths
end

val FDOM_camlPEG = save_thm(
  "FDOM_camlPEG",
  SIMP_CONV (srw_ss()) [camlPEG_def,
                        finite_mapTheory.FRANGE_FUPDATE_DOMSUB,
                        finite_mapTheory.DOMSUB_FUPDATE_THM,
                        finite_mapTheory.FUPDATE_LIST_THM]
            ``FDOM camlPEG.rules``);

val spec0 =
    peg_nt_thm |> Q.GEN `G`  |> Q.ISPEC `camlPEG`
               |> SIMP_RULE (srw_ss()) [FDOM_camlPEG]
               |> Q.GEN `n`

val distinct_ths = let
  val ntlist = TypeBase.constructors_of ``:camlNT``
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

Theorem camlPEG_exec_thm[compute] =
  TypeBase.constructors_of ``:camlNT``
    |> map (fn t => ISPEC (sumSyntax.mk_inl(t, “:num”)) spec0)
    |> map (SIMP_RULE bool_ss (camlpeg_rules_applied @ distinct_ths @
                               [sumTheory.INL_11]))
    |> LIST_CONJ;

val test =
  time EVAL “peg_exec camlPEG (pnt nStart)
             (map_loc [
                  IntT 3; StarT; IntT 4; SymbolT "/"; IntT (-2);
              ] 0)
             [] NONE [] done failed”;

val test2 =
  time EVAL “peg_exec camlPEG (pnt nStart)
             (map_loc [
                  IntT 3; StarT; IntT 4;
              ] 0)
             [] NONE [] done failed”;

val test3 =
  time EVAL “peg_exec camlPEG (pnt nStart)
             (map_loc [
                  IntT 3; LessT; IdentT "foo";
              ] 0)
             [] NONE [] done failed”;

val test4 =
  time EVAL “peg_exec camlPEG (pnt nStart)
             (map_loc [
                  IntT 3; ColonsT; IdentT "xs";
              ] 0)
             [] NONE [] done failed”;

val test5 =
  time EVAL “peg_exec camlPEG (pnt nStart)
             (map_loc [
                  ColonsT; IdentT "xs";
              ] 0)
             [] NONE [] done failed”;

val test6 =
  time EVAL “peg_exec camlPEG (pnt nStart)
             (map_loc [
                  IdentT "xs";
              ] 0)
             [] NONE [] done failed”;

val test7 =
  time EVAL “peg_exec camlPEG (pnt nStart)
             (map_loc [
                  IdentT "x"; ColonsT;
                  IdentT "y"; ColonsT;
                  IdentT "xs";
              ] 0)
             [] NONE [] done failed”;

val test8 =
  time EVAL “peg_exec camlPEG (pnt nStart)
             (map_loc [
                  LparT;
                  IdentT "x"; ColonsT;
                  IdentT "y";
                  RparT;
                  ColonsT;
                  IdentT "xs";
              ] 0)
             [] NONE [] done failed”;

val test9 =
  time EVAL “peg_exec camlPEG (pnt nStart)
             (map_loc [
                  IdentT "y";
                  SymbolT "@<<";
                  IdentT "xs";
              ] 0)
             [] NONE [] done failed”;

(* -------------------------------------------------------------------------
 * Running the lexer, and then the parser
 * ------------------------------------------------------------------------- *)

Overload camlpegexec =
  “λn t. peg_exec camlPEG (pnt n) t [] NONE [] done failed”;

Definition destResult_def:
  destResult (Result (Success [] x eo)) = INR (x, eo) ∧
  destResult (Result (Success ((_,l)::_) _ _)) =
    INL (l, "Expected to be at EOF") ∧
  destResult (Result (Failure fl fe)) = INL (fl, fe) ∧
  destResult _ =
    INL (unknown_loc, "Something catastrophic happened")
End

Definition run_prog_def:
  run_prog input =
    let toks = lexer_fun input in
    let errs = FILTER ($= LexErrorT o FST) toks in
      if errs ≠ [] then
        INL (SND (HD errs), "Lexer error")
      else
        destResult (camlpegexec nStart toks)
End

Definition parse_def:
  parse input =
    case run_prog input of
      INL (Locs (POSN r1 c1) (POSN r2 c2), err) =>
        "Failure: " ++ err ++ "\nbetween (" ++
        toString r1 ++ ", " ++ toString c1 ++ ") and (" ++
        toString r2 ++ ", " ++ toString c2 ++ ").\n"
    | INR (tree, _) => "Success!\n"
End

fun run_parser str =
  let
    val holstr = stringSyntax.fromMLstring str
    val th = EVAL “parse ^holstr” |> SIMP_RULE (srw_ss()) [camlPEG_def]
    val strtm = rhs (concl th)
    val outstr = stringSyntax.fromHOLstring strtm
  in
    print outstr
  end;

fun run_parser_file file =
  let
    val ins = TextIO.openIn file
    val str = TextIO.inputAll ins
    val _ = TextIO.closeIn ins
  in
    run_parser str
  end;

val test1 = run_parser ":: d ? 4"
val test2 = run_parser "1 + ? 4"
val test3 = run_parser "1 + 33 / (a_b_cdef :: 4)"
val test4 = run_parser "abcdef \\s"
val test5 = run_parser "if let x = True in x then 4 else 3";
val test6 = run_parser "if let x = true in x then 4 else 3";
val test7 = run_parser "if let x = * true in x then 4 else 3 + 4";
val test8 = run_parser "let x = [(1;2);(3;4)] in x"
val test9 = run_parser "let x = [1;2;3;4] in x"
val test10 = run_parser "let x = [1; ;2;3;4] in x"
val test11 = run_parser "let x = 3 and y = 4;; (let z = [3] in z) ;;"

val _ = export_theory ();

