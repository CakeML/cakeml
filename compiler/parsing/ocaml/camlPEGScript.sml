(*
  Definition of a PEG for (a subset of) OCaml.
 *)

open preamble caml_lexTheory;
open pegexecTheory pegTheory;
open finite_mapSyntax;
open mlstringTheory;

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

Definition tokPragma_def:
  tokPragma =
    tok (λt. (do s <- destPragma t; return () od) = SOME ()) mktokLf
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
  validPrefixSym s ⇔
    s ≠ "" ∧
    (HD s = #"!" ∨ HD s = #"?" ∨ HD s = #"~" ∧ 2 ≤ LENGTH s) ∧
    EVERY validOpChar (TL s)
End

Definition validInfixSym_def:
  validInfixSym s ⇔
    s ≠ "" ∧
    (validCoreOpChar (HD s) ∨ HD s = #"%" ∨ HD s = #"<" ∨
     HD s = #"#" ∧ 2 ≤ LENGTH s) ∧
    EVERY validOpChar (TL s)
End

Definition validMultOp_def:
  validMultOp s ⇔
    s ≠ "" ∧
    (s = "%" ∨
     s = "/" ∨
     ((HD s = #"*" ∨ HD s = #"%" ∨ HD s = #"/") ∧
        2 ≤ LENGTH s ∧ EVERY validOpChar (TL s)))
End

Definition validRelOp_def:
  validRelOp s ⇔
    s ≠ "" ∧
    (HD s = #"<" ∨ HD s = #">" ∨ HD s = #"|" ∨
     HD s = #"&" ∨ HD s = #"$") ∧
    2 ≤ LENGTH s ∧
    EVERY validOpChar (TL s)
End

Definition validAddOp_def:
  validAddOp s ⇔
    s ≠ "" ∧
    (HD s = #"+" ∨ HD s = #"-") ∧
    2 ≤ LENGTH s ∧
    EVERY validOpChar (TL s)
End

Definition validRelOp_def:
  validRelOp s ⇔
    s ≠ "" ∧
    (HD s = #"=" ∨ HD s = #"<" ∨ HD s = #">" ∨ HD s = #"|" ∨
     HD s = #"&" ∨ HD s = #"$") ∧
    2 ≤ LENGTH s ∧
    EVERY validOpChar (TL s)
End

Definition validShiftOp_def:
  validShiftOp s ⇔
    IS_PREFIX s "**" ∧
    EVERY validOpChar (TL (TL s))
End

Definition validCatOp_def:
  validCatOp s ⇔
    s ≠ "" ∧
    (HD s = #"@" ∨ HD s = CHR 94) ∧
    EVERY validOpChar (TL s)
End

Definition idChar_def:
  idChar P = EVERY (λc. P c ∨ c = #"_" ∨ c = #"'" ∨ isDigit c)
End

(* Modules and type constructors according to HOL light are words that start
 * with a capital letter and then only lowercase letters, digits or ticks.
 * There has to be at least one character in the tail of the string, and at
 * least one of those need to be lowercase.
 *)

Definition identUpperLower_def:
  identUpperLower s ⇔
    s ≠ "" ∧
    isUpper (HD s) ∧
    idChar isLower (TL s) ∧
    EXISTS isLower (TL s)
End

(* Names of values according to HOL light are all combinations of identifier
 * characters (alphanumerics, underscore and tick) _except_ those that are
 * module names or type constructors. In particular, if there are letters in
 * the tail of the string, then at least one of those letters must be
 * uppercase.
 *)

Definition identMixed_def:
  identMixed s ⇔
    s ≠ "" ∧
    idChar isAlpha (TL s) ∧
    ((isLower (HD s) ∨ HD s = #"_") ∨
     (isUpper (HD s) ∧
      (EXISTS isAlpha (TL s) ⇒ EXISTS isUpper (TL s))))
End

(* Names of types start with a lowercase letter or underscore.
 *)

Definition identLower_def:
  identLower s ⇔
    s ≠ "" ∧
    (isLower (HD s) ∨ HD s = #"_") ∧
    idChar isAlpha (TL s)
End

Datatype:
  camlNT =
    (* hol-light specific operators *)
    | nEHolInfix | nHolInfixOp
    (* different sorts of names *)
    | nValuePath | nValueName
    | nConstr | nConstrName
    | nTypeConstr | nTypeConstrName
    | nModulePath | nModuleName
    | nModTypePath | nModTypeName
    | nFieldName
    | nOperatorName
    (* expressions *)
    | nLiteral | nIdent | nEBase | nEList
    | nEApp | nEConstr | nEFunapp | nEAssert | nELazy
    | nEPrefix | nENeg | nEShift | nEMult
    | nERecProj | nERecUpdate | nERecCons
    | nEAdd | nECons | nECat | nERel
    | nEAnd | nEOr | nEProd | nEAssign | nEIf | nESeq
    | nEMatch | nETry | nEFun | nEFunction | nELet | nELetRec
    | nEWhile | nEFor | nExpr
    | nEUnclosed (* expressions that bind everything to the right *)
    (* record updates *)
    | nUpdate | nUpdates | nFieldDec | nFieldDecs
    (* pattern matches *)
    | nLetBinding | nLetBindings | nLetRecBinding | nLetRecBindings
    | nPatternMatch | nPatternMatches
    (* type definitions *)
    | nTypeDefinition | nTypeDef | nTypeDefs | nTypeParams | nTypeInfo
    | nTypeRepr | nTypeReprs | nConstrDecl | nConstrArgs | nRecord
    | nExcDefinition
    (* patterns *)
    | nPAny | nPList | nPPar | nPBase | nPCons | nPAs | nPOps | nPattern
    | nPatterns
    (* types *)
    | nTypeList | nTypeLists
    | nTVar | nTBase | nTConstr | nTProd | nTFun | nType
    (* module types *)
    | nSigSpec | nSigItems | nSigItem | nModTypeAssign | nModTypeAsc
    | nModAscApp | nModAscApps | nValType | nExcType | nModuleTypeDef
    | nIncludeMod | nOpenMod
    (* definitions *)
    | nDefinition | nTopLet | nTopLetRec | nModuleItem | nModuleItems | nOpen
    | nModExpr | nModuleDef | nModuleType
    | nSemis | nExprItem | nExprItems | nDefItem
    (* misc *)
    | nShiftOp | nMultOp | nAddOp | nRelOp | nAndOp | nOrOp | nCatOp | nPrefixOp
    | nAssignOp | nStart
    (* Declarations through CakeML pragmas *)
    | nCakeMLPragma
End

(* Definition of the OCaml PEG.
 *)

Definition camlPEG_def[nocompute]:
  camlPEG = <|
    anyEOF   := "Unexpected end-of-file";
    tokFALSE := "Unexpected token";
    tokEOF   := "Expected token, found end-of-file";
    notFAIL  := "Not combinator failed";
    start := pnt nStart;
    rules := FEMPTY |++ [
      (* -- CakeML code pragmas -------------------------------------------- *)
      (INL nCakeMLPragma,
       pegf (tokPragma) (bindNT nCakeMLPragma));
      (* -- HOL Light specific ops ----------------------------------------- *)
      (INL nHolInfixOp,
       pegf (choicel [tokeq FuncompT; tokeq F_FT; tokeq THEN_T; tokeq THENC_T;
                      tokeq THENL_T; tokeq THEN_TCL_T; tokeq ORELSE_T;
                      tokeq ORELSEC_T; tokeq ORELSE_TCL_T])
            (bindNT nHolInfixOp));
      (* -- Names and paths ------------------------------------------------ *)
      (INL nValueName,
       choicel [pegf (tokIdP identMixed) (bindNT nValueName);
                seql [tokeq LparT; pnt nOperatorName; tokeq RparT]
                     (bindNT nValueName)]);
      (INL nOperatorName,
       pegf (choicel [pnt nShiftOp;
                      pnt nMultOp;
                      pnt nAddOp;
                      pnt nRelOp;
                      pnt nAndOp;
                      pnt nOrOp;
                      pnt nHolInfixOp;
                      pnt nCatOp;
                      pnt nPrefixOp;
                      pnt nAssignOp ])
            (bindNT nOperatorName));
      (INL nConstrName,
       pegf (tokIdP identUpperLower) (bindNT nConstrName));
      (INL nTypeConstrName,
       pegf (tokIdP identLower) (bindNT nTypeConstrName));
      (INL nModuleName,
       pegf (tokIdP identUpperLower) (bindNT nModuleName));
      (INL nFieldName,
       pegf (tokIdP identLower) (bindNT nFieldName));
      (INL nValuePath,
       seql [try (seql [pnt nModulePath; tokeq DotT] I); pnt nValueName]
            (bindNT nValuePath));
      (* Can't use nModulePath in nConstr, because it would parse the
         nConstrName as a nModuleName (because they're the same). But we can
         do this:
            constr ::= mod-name "." constr / constr-name
       *)
      (INL nConstr,
       pegf (choicel [seql [pnt nModuleName; tokeq DotT; pnt nConstr] I;
                      pnt nConstrName])
            (bindNT nConstr));
      (INL nTypeConstr,
       seql [try (seql [pnt nModulePath; tokeq DotT] I); pnt nTypeConstrName]
            (bindNT nTypeConstr));
      (INL nModulePath,
       seql [pnt nModuleName; try (seql [tokeq DotT; pnt nModulePath] I)]
            (bindNT nModulePath));
      (INL nModTypeName,
       pegf (tokIdP (λx. T)) (bindNT nModTypeName));
      (* Can't use nModulePath in nModTypePath because of similar reasons to
         nConstr (there's some ambiguity).
       *)
      (INL nModTypePath,
       pegf (choicel [seql [pnt nModuleName; tokeq DotT; pnt nModTypePath] I;
                      pnt nModTypeName])
            (bindNT nModTypePath));
      (* -- Definitions (module items) ------------------------------------- *)
      (INL nSemis,
       seql [tokeq SemisT; try (pnt nSemis)]
            (bindNT nSemis));
      (INL nExprItems,
       seql [try (pnt nSemis); pnt nExpr]
            (bindNT nExprItems));
      (INL nExprItem,
       seql [pnt nSemis; pnt nExpr]
            (bindNT nExprItem));
      (INL nDefItem,
       seql [try (pnt nSemis); pnt nDefinition]
            (bindNT nDefItem));
      (INL nModuleItems,
       seql [choicel [pnt nExprItems; pnt nDefItem];
             try (pnt nModuleItem);
             try (pnt nSemis)]
            (bindNT nModuleItems));
      (INL nModuleItem,
       seql [choicel [pnt nExprItem; pnt nDefItem];
             try (pnt nModuleItem)]
            (bindNT nModuleItem));
      (INL nTopLet,
       seql [tokeq LetT; pnt nLetBindings]
            (bindNT nTopLet));
      (INL nTopLetRec,
       seql [tokeq LetT; tokeq RecT; pnt nLetRecBindings]
            (bindNT nTopLetRec));
      (INL nOpen,
       seql [tokeq OpenT; pnt nModulePath]
            (bindNT nOpen));
      (INL nModExpr,
       pegf (choicel [pnt nModulePath;
                      seql [tokeq StructT; try (pnt nModuleItems); tokeq EndT] I])
            (bindNT nModExpr));
      (INL nModuleDef,
       seql [tokeq ModuleT; pnt nModuleName;
             try (seql [tokeq ColonT; pnt nModuleType] I);
             tokeq EqualT; pnt nModExpr]
            (bindNT nModuleDef));
      (INL nDefinition,
       pegf (choicel [pnt nTopLetRec;
                      pnt nTopLet;
                      pnt nTypeDefinition;
                      pnt nExcDefinition;
                      pnt nOpen;
                      pnt nModuleTypeDef;
                      pnt nModuleDef;
                      (* CakeML code pragmas: *)
                      pnt nCakeMLPragma;
                      (* include moduleexpr *)
                      (* functor versions of the moduletype thing *)
                      ])
            (bindNT nDefinition));
      (* -- Module types (signatures) -------------------------------------- *)
      (INL nExcType,
       seql [tokeq ExceptionT; pnt nConstrDecl]
            (bindNT nExcType));
      (INL nValType,
       seql [tokeq ValT; pnt nValueName; tokeq ColonT; pnt nType]
            (bindNT nValType));
      (INL nModAscApp,
       seql [tokeq LparT; pnt nModuleName; tokeq ColonT;
             pnt nModuleType; tokeq RparT]
            (bindNT nModAscApp));
      (INL nModAscApps,
       seql [pnt nModAscApp; try (pnt nModAscApps)]
            (bindNT nModAscApps));
      (INL nModTypeAsc,
       seql [tokeq ModuleT; tokeq TypeT; pnt nModuleName;
             try (pnt nModAscApps);
             tokeq ColonT; pnt nModuleType]
            (bindNT nModTypeAsc));
      (INL nModTypeAssign,
       seql [tokeq ModuleT; tokeq TypeT; pnt nModTypeName;
             try (seql [tokeq EqualT; pnt nModuleType] I)]
            (bindNT nModTypeAssign));
      (INL nOpenMod,
       seql [tokeq OpenT; pnt nModulePath]
            (bindNT nOpenMod));
      (INL nIncludeMod,
       seql [tokeq IncludeT; pnt nModulePath]
            (bindNT nIncludeMod));
      (INL nSigItem,
       pegf (choicel [pnt nTypeDefinition;
                      pnt nExcType;
                      pnt nValType;
                      pnt nModTypeAsc;
                      pnt nModTypeAssign;
                      pnt nOpenMod;
                      pnt nIncludeMod;
                     ])
            (bindNT nSigItem));
      (INL nSigItems,
       seql [pnt nSigItem; try (pnt nSemis); try (pnt nSigItems)]
            (bindNT nSigItems));
      (INL nSigSpec,
       seql [tokeq SigT; try (pnt nSigItems); tokeq EndT]
            (bindNT nSigSpec));
      (INL nModuleType,
       pegf (choicel [pnt nModTypePath;
                      pnt nSigSpec;
                      seql [tokeq LparT; pnt nModuleType; tokeq RparT] I;
                      (* functor syntax *)])
            (bindNT nModuleType));
      (INL nModuleTypeDef,
       seql [tokeq ModuleT; tokeq TypeT; pnt nModTypeName; tokeq EqualT;
             pnt nModuleType]
            (bindNT nModuleTypeDef));
      (* -- Typedef -------------------------------------------------------- *)
      (INL nExcDefinition,
       seql [tokeq ExceptionT;
             choicel [seql [pnt nConstrName; tokeq EqualT; pnt nConstr] I;
                      pnt nConstrDecl]]
            (bindNT nExcDefinition));
      (INL nTypeDefinition,
       seql [tokeq TypeT; try (tokeq NonrecT); pnt nTypeDefs]
            (bindNT nTypeDefinition));
      (INL nTypeDef,
       seql [try (pnt nTypeParams); pnt nTypeConstrName;
             try (pnt nTypeInfo)]
            (bindNT nTypeDef));
      (INL nTypeDefs,
       seql [pnt nTypeDef; try (seql [tokeq AndT; pnt nTypeDefs] I)]
            (bindNT nTypeDefs));
      (INL nTypeParams,
       choicel [pegf (pnt nTVar) (bindNT nTypeParams);
                seql [tokeq LparT; pnt nTVar;
                      rpt (seql [tokeq CommaT; pnt nTVar] I) FLAT;
                      tokeq RparT]
                     (bindNT nTypeParams)]);
      (INL nTypeInfo,
       seql [tokeq EqualT;
             choicel [pnt nType; pnt nTypeRepr]]
            (bindNT nTypeInfo));
      (INL nTypeRepr,
       seql [try (tokeq BarT); pnt nConstrDecl; try (pnt nTypeReprs)]
            (bindNT nTypeRepr));
      (INL nTypeReprs,
       seql [tokeq BarT; pnt nConstrDecl; try (pnt nTypeReprs)]
            (bindNT nTypeReprs));
      (INL nConstrDecl,
       seql [pnt nConstrName;
             try (seql [tokeq OfT; choicel [pnt nConstrArgs; pnt nRecord]] I)]
            (bindNT nConstrDecl));
      (INL nRecord,
       seql [tokeq LbraceT; pnt nFieldDecs; try (tokeq SemiT); tokeq RbraceT]
            (bindNT nRecord));
      (INL nFieldDecs,
       seql [pnt nFieldDec; try (seql [tokeq SemiT; pnt nFieldDecs] I)]
            (bindNT nFieldDecs));
      (INL nFieldDec,
       seql [pnt nFieldName; tokeq ColonT; pnt nType]
            (bindNT nFieldDec));
      (INL nConstrArgs,
       seql [pnt nTConstr; rpt (seql [tokeq StarT; pnt nTConstr] I) FLAT]
            (bindNT nConstrArgs));
      (* -- Type5 ---------------------------------------------------------- *)
      (INL nTypeList,
       seql [pnt nType; tokeq CommaT; pnt nTypeLists]
            (bindNT nTypeList));
      (INL nTypeLists,
       seql [pnt nType; try (seql [tokeq CommaT; pnt nTypeLists] I)]
            (bindNT nTypeLists));
      (INL nTVar,
       seql [tokeq TickT; pnt nIdent] (bindNT nTVar));
      (INL nTBase,
       pegf (choicel [seql [tokeq LparT; pnt nType; tokeq RparT] I;
                      seql [tokeq LparT; pnt nTypeList; tokeq RparT;
                            pnt nTypeConstr] I;
                      pnt nTVar])
            (bindNT nTBase));
      (* -- Type4 ---------------------------------------------------------- *)
      (INL nTConstr,
       choicel [seql [try (pnt nTBase); pnt nTypeConstr;
                      rpt (pnt nTypeConstr) FLAT]
                     (bindNT nTConstr);
                pegf (pnt nTBase) (bindNT nTConstr)]);
      (* -- Type3 ---------------------------------------------------------- *)
      (INL nTProd,
       seql [pnt nTConstr; rpt (seql [tokeq StarT; pnt nTConstr] I) FLAT]
            (bindNT nTProd));
      (* -- Type2 ---------------------------------------------------------- *)
      (INL nTFun,
       seql [pnt nTProd; try (seql [tokeq RarrowT; pnt nTFun] I)]
            (bindNT nTFun));
      (* -- Type ----------------------------------------------------------- *)
      (INL nType,
       pegf (pnt nTFun) (bindNT nType));
      (* -- Expr16 --------------------------------------------------------- *)
      (INL nEList,
       seql [tokeq LbrackT;
             try (seql [pnt nEIf;
                        rpt (seql [tokeq SemiT; pnt nEIf] I) FLAT;
                        try (tokeq SemiT)] I);
             tokeq RbrackT]
            (bindNT nEList));
      (INL nLiteral,
       choicel [
         tok isInt    (bindNT nLiteral o mktokLf);
         tok isString (bindNT nLiteral o mktokLf);
         tok isChar   (bindNT nLiteral o mktokLf);
         tok (λx. MEM x [TrueT; FalseT]) (bindNT nLiteral o mktokLf)]);
      (INL nIdent,
       tok isIdent (bindNT nIdent o mktokLf));
      (INL nUpdate,
       seql [pnt nFieldName; tokeq EqualT; pnt nEIf]
            (bindNT nUpdate));
      (INL nUpdates,
       seql [pnt nUpdate; try (seql [tokeq SemiT; pnt nUpdates] I)]
            (bindNT nUpdates));
      (INL nERecUpdate,
       seql [tokeq LbraceT; pnt nExpr; tokeq WithT; pnt nUpdates;
             try (tokeq SemiT); tokeq RbraceT]
            (bindNT nERecUpdate));
      (INL nEBase,
       choicel [
         pegf (pnt nLiteral) (bindNT nEBase);
         pegf (pnt nValuePath) (bindNT nEBase);
         pegf (pnt nConstr) (bindNT nEBase);
         pegf (pnt nEList) (bindNT nEBase);
         pegf (pnt nERecUpdate) (bindNT nEBase);
         seql [tokeq LparT; tokeq RparT] (bindNT nEBase); (* unit *)
         seql [tokeq BeginT; tokeq EndT] (bindNT nEBase); (* unit *)
         seql [tokeq LparT; pnt nExpr;
               try (seql [tokeq ColonT; pnt nType] I);
               tokeq RparT] (bindNT nEBase);
         seql [tokeq BeginT; pnt nExpr; tokeq EndT] (bindNT nEBase)
       ]);
      (* -- Expr15 --------------------------------------------------------- *)
      (INL nPrefixOp,
       pegf (tokSymP validPrefixSym)
            (bindNT nPrefixOp));
      (INL nEPrefix,
       seql [try (pnt nPrefixOp); pnt nEBase] (bindNT nEPrefix));
      (* -- Expr14.5 ------------------------------------------------------- *)
      (INL nERecProj,
       seql [pnt nEPrefix;
             try (seql [tokeq DotT; pnt nFieldName] I)]
            (bindNT nERecProj));
      (* -- Expr14 --------------------------------------------------------- *)
      (INL nEAssert,
       seql [tokeq AssertT; pnt nERecProj] (bindNT nEAssert));
      (INL nELazy,
       seql [tokeq LazyT; pnt nERecProj] (bindNT nELazy));
      (INL nEConstr,
       seql [pnt nConstr; pnt nERecProj] (bindNT nEConstr));
      (INL nERecCons,
       seql [pnt nConstr;
             tokeq LbraceT; pnt nUpdates; try (tokeq SemiT); tokeq RbraceT]
            (bindNT nERecCons));
      (INL nEFunapp,
       seql [pnt nERecProj; rpt (pnt nERecProj) FLAT]
            (λl. case l of
                   [] => []
                 | h::t => [FOLDL (λa b. mkNd (INL nEFunapp) [a; b])
                                  (mkNd (INL nEFunapp) [h]) t]));
      (INL nEApp,
       pegf (choicel (MAP pnt [nELazy; nEAssert; nERecCons; nEConstr; nEFunapp;
                               nERecProj]))
            (bindNT nEApp));
      (* -- Expr13 --------------------------------------------------------- *)
      (INL nEUnclosed,
       pegf (choicel [
               pnt nELetRec; pnt nELet; pnt nEMatch; pnt nEFun; pnt nEFunction;
               pnt nETry; pnt nEWhile; pnt nEFor; pnt nEApp])
            (bindNT nEUnclosed));
      (INL nELetRec,
       seql [tokeq LetT; tokeq RecT; pnt nLetRecBindings;
             tokeq InT; pnt nExpr]
            (bindNT nELetRec));
      (INL nELet,
       seql [tokeq LetT; pnt nLetBindings;
             tokeq InT; pnt nExpr]
            (bindNT nELet));
      (INL nEMatch,
       seql [tokeq MatchT; pnt nExpr; tokeq WithT; pnt nPatternMatch]
            (bindNT nEMatch));
      (INL nEFun,
       seql [tokeq FunT; pnt nPatterns;
             try (seql [tokeq ColonT; pnt nType] I);
             tokeq RarrowT; pnt nExpr]
            (bindNT nEFun));
      (INL nEFunction,
       seql [tokeq FunctionT; pnt nPatternMatch]
            (bindNT nEFunction));
      (INL nETry,
       seql [tokeq TryT; pnt nExpr; tokeq WithT; pnt nPatternMatch]
            (bindNT nETry));
      (INL nEWhile,
       seql [tokeq WhileT; pnt nExpr; tokeq DoT; pnt nExpr; tokeq DoneT]
            (bindNT nEWhile));
      (INL nEFor,
       seql [tokeq ForT; pnt nValueName; tokeq EqualT; pnt nExpr;
             choicel [tokeq ToT; tokeq DowntoT]; pnt nExpr;
             tokeq DoT; pnt nExpr; tokeq DoneT]
            (bindNT nEFor));
      (* -- Expr12 --------------------------------------------------------- *)
      (INL nENeg,
       seql [try (choicel [tokeq MinusT; tokeq MinusFT]);
             (* try the non-closed expressions or an application *)
             pnt nEUnclosed]
            (bindNT nENeg));
      (* -- Expr11 --------------------------------------------------------- *)
      (INL nShiftOp,
       pegf (choicel [tokSymP validShiftOp; tokeq LslT; tokeq LsrT; tokeq AsrT])
            (bindNT nShiftOp));
      (INL nEShift,
       seql [pnt nENeg; try (seql [pnt nShiftOp; pnt nEShift] I)]
            (bindNT nEShift));
      (* -- Expr10 --------------------------------------------------------- *)
      (INL nMultOp,
       pegf (choicel [tokeq StarT; tokeq ModT; tokeq LandT; tokeq LorT;
                      tokeq LxorT; tokSymP validMultOp])
            (bindNT nMultOp));
      (INL nEMult,
       peg_linfix (INL nEMult) (pnt nEShift) (pnt nMultOp));
      (* -- Expr9 ---------------------------------------------------------- *)
      (INL nAddOp,
       pegf (choicel [tokeq PlusT; tokeq MinusT; tokeq MinusFT;
                      tokSymP validAddOp])
            (bindNT nAddOp));
      (INL nEAdd,
       peg_linfix (INL nEAdd) (pnt nEMult) (pnt nAddOp));
      (* -- Expr8 ---------------------------------------------------------- *)
      (INL nECons,
       seql [pnt nEAdd; try (seql [tokeq ColonsT; pnt nECons] I)]
            (bindNT nECons));
      (* -- Expr7 ---------------------------------------------------------- *)
      (INL nCatOp,
       pegf (tokSymP validCatOp)
            (bindNT nCatOp));
      (INL nECat,
       seql [pnt nECons; try (seql [pnt nCatOp; pnt nECat] I)]
            (bindNT nECat));
      (* -- Expr6 ---------------------------------------------------------- *)
      (INL nRelOp,
       pegf (choicel [tokeq EqualT; tokeq LessT; tokeq GreaterT; tokeq NeqT;
                      tokSymP validRelOp])
            (bindNT nRelOp));
      (INL nERel,
       peg_linfix (INL nERel) (pnt nECat) (pnt nRelOp));
      (* -- Expr5 ---------------------------------------------------------- *)
      (INL nAndOp,
       pegf (choicel [tokeq AmpT; tokeq AndalsoT])
            (bindNT nAndOp));
      (INL nEAnd,
       seql [pnt nERel; try (seql [pnt nAndOp; pnt nEAnd] I)]
            (bindNT nEAnd));
      (* -- Expr4 ---------------------------------------------------------- *)
      (INL nOrOp,
       pegf (choicel [tokeq OrelseT; tokeq OrT])
            (bindNT nOrOp));
      (INL nEOr,
       seql [pnt nEAnd; try (seql [pnt nOrOp; pnt nEOr] I)]
            (bindNT nEOr));
      (* -- Expr 3.5 ------------------------------------------------------- *)
      (INL nEHolInfix,
       peg_linfix (INL nEHolInfix) (pnt nEOr) (pnt nHolInfixOp));
      (* -- Expr3 ---------------------------------------------------------- *)
      (INL nEProd,
       seql [pnt nEHolInfix;
             rpt (seql [tokeq CommaT; pnt nEHolInfix] I) FLAT]
            (bindNT nEProd));
      (* -- Expr2: assignments --------------------------------------------- *)
      (INL nAssignOp,
       pegf (choicel [tokeq UpdateT; tokeq LarrowT])
            (bindNT nAssignOp));
      (INL nEAssign,
       seql [pnt nEProd; try (seql [pnt nAssignOp; pnt nEAssign] I)]
            (bindNT nEAssign));
      (* -- Expr1 ---------------------------------------------------------- *)
      (INL nEIf,
       pegf (choicel [seql [tokeq IfT; pnt nExpr; tokeq ThenT; pnt nEIf;
                            try (seql [tokeq ElseT; pnt nEIf] I)] I;
                      pnt nEAssign])
            (bindNT nEIf));
      (* -- Expr: ---------------------------------------------------------- *)
      (INL nESeq,
       seql [pnt nEIf; try (seql [tokeq SemiT; pnt nExpr] I)]
            (bindNT nESeq));
      (INL nExpr,
       pegf (choicel [pnt nESeq])
            (bindNT nExpr));
      (* -- Pattern matches ------------------------------------------------ *)
      (INL nPatternMatch,
       seql [try (tokeq BarT); pnt nPatternMatches]
            (bindNT nPatternMatch));
      (INL nPatternMatches,
       seql [pnt nPattern;
             try (seql [tokeq WhenT; pnt nExpr] I);
             tokeq RarrowT; pnt nExpr;
             try (seql [tokeq BarT; pnt nPatternMatches] I)]
            (bindNT nPatternMatches));
      (* -- Let bindings --------------------------------------------------- *)
      (INL nLetRecBinding,
       seql [pnt nValueName; pnt nPatterns;
             try (seql [tokeq ColonT; pnt nType] I);
             tokeq EqualT; pnt nExpr]
            (bindNT nLetRecBinding));
      (INL nLetRecBindings,
       seql [pnt nLetRecBinding; try (seql [tokeq AndT; pnt nLetRecBindings] I)]
            (bindNT nLetRecBindings));
      (INL nLetBinding,
       pegf (choicel [seql [pnt nPattern; tokeq EqualT; pnt nExpr] I;
                      seql [pnt nValueName; pnt nPatterns;
                            try (seql [tokeq ColonT; pnt nType] I);
                            tokeq EqualT; pnt nExpr] I])
            (bindNT nLetBinding));
      (INL nLetBindings,
       seql [pnt nLetBinding; try (seql [tokeq AndT; pnt nLetBindings] I)]
            (bindNT nLetBindings));
      (* -- Pat3 ----------------------------------------------------------- *)
      (INL nPAny, (* ::= '_' *)
       pegf (tokeq AnyT) (bindNT nPAny));
      (INL nPList, (* ::= '[' (p ';')* p? ']' *)
       seql [tokeq LbrackT;
             rpt (seql [pnt nPattern; tokeq SemiT] I) FLAT; try (pnt nPattern);
             tokeq RbrackT]
            (bindNT nPList));
      (INL nPPar, (* ::= '(' (p (':' ty)?)? ')' *)
       seql [tokeq LparT;
             try (seql [pnt nPattern;
                        try (seql [tokeq ColonT; pnt nType] I)] I);
             tokeq RparT]
            (bindNT nPPar));
      (INL nPBase, (* ::= any / var / lit / list / '(' p ')' *)
       pegf (choicel [pnt nLiteral; pnt nValueName; pnt nPAny; pnt nPList;
                      pnt nPPar])
            (bindNT nPBase));
      (* -- Pat2 ----------------------------------------------------------- *)
      (INL nPCons, (* ::= constr p? *)
       pegf (choicel [seql [pnt nConstr; try (pnt nPBase)] I;
                      pnt nPBase])
            (bindNT nPCons));
      (INL nPAs, (* ::= p ('as' id)* *)
       seql [pnt nPCons; rpt (seql [tokeq AsT; pnt nIdent] I) FLAT]
            (bindNT nPAs));
      (* -- Pat1 ----------------------------------------------------------- *)
      (INL nPOps,
       seql [pnt nPAs; rpt (seql [tok (λt. t = ColonsT ∨ t = CommaT ∨ t = BarT)
                                      mktokLf; pnt nPAs] I) FLAT]
            (bindNT nPOps));
      (INL nPattern,
       pegf (pnt nPOps) (bindNT nPattern));
      (INL nPatterns,
       seql [pnt nPattern; try (pnt nPatterns)]
            (bindNT nPatterns));
      (INL nStart,
       seql [try (pnt nModuleItems)] (bindNT nStart))
      ] |>
End

(* -------------------------------------------------------------------------
 * Some of this is used in proving parser side conditions in translation later.
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

(*
Overload camlpegexec =
  “λn t. peg_exec camlPEG (pnt n) t [] NONE [] done failed”;

val t1 = rhs $ concl $ time EVAL “lexer_fun "x::(_ as p)"”;
val t2 = time EVAL “camlpegexec nPattern ^t1”;
val t3 = t2 |> concl |> rhs |> rand |> rator |> rand |> listSyntax.dest_list
         |> #1 |> hd
val t4 = EVAL “ptree_Pattern ^t3”;
 *)

Theorem frange_image[local]:
  FRANGE fm = IMAGE (FAPPLY fm) (FDOM fm)
Proof
  simp[finite_mapTheory.FRANGE_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

val camlpeg_rules_applied = fetch "-" "camlpeg_rules_applied";

val peg_range =
    SIMP_CONV (srw_ss())
              [FDOM_camlPEG, frange_image, camlpeg_rules_applied]
              “FRANGE camlPEG.rules”;

Theorem peg_start[local] = SIMP_CONV(srw_ss()) [camlPEG_def] “camlPEG.start”;

val wfpeg_rwts =
    pegTheory.wfpeg_cases
    |> ISPEC “camlPEG”
    |> (fn th => map (fn t => Q.SPEC t th)
                       [`seq e1 e2 f`, `choice e1 e2 f`, `tok P f`,
                        `any f`, `empty v`, `not e v`, `rpt e f`,
                        `choicel []`, `choicel (h::t)`, `tokeq t`,
                        `pegf e f`, ‘tokSymP P’])
    |> map (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss())
                                            [choicel_def, seql_def,
                                             tokeq_def, tokSymP_def,
                                             pegf_def])));

val wfpeg_pnt =
    pegTheory.wfpeg_cases
    |> ISPEC “camlPEG”
    |> Q.SPEC ‘pnt n’
    |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [pnt_def]))

val peg0_rwts =
  pegTheory.peg0_cases
  |> ISPEC “camlPEG” |> CONJUNCTS
  |> map (fn th => map (fn t => Q.SPEC t th)
                       [`tok P f`, `choice e1 e2 f`,
                        ‘seq e1 e2 f’, ‘tokSymP P’,
                        `tokeq t`, `empty l`, `not e v`])
  |> List.concat
  |> map (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss())
                                          [tokeq_def, tokSymP_def])));

val pegfail_t = “pegfail”
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

val pegnt_case_ths =
    pegTheory.peg0_cases
    |> ISPEC “camlPEG” |> CONJUNCTS
    |> map (Q.SPEC ‘pnt n’)
    |> map (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [pnt_def])))

Theorem peg0_pegf:
  peg0 G (pegf s f) = peg0 G s
Proof
  simp [pegf_def]
QED

Theorem peg0_seql:
  (peg0 G (seql [] f) ⇔ T) ∧
  (peg0 G (seql (h::t) f) ⇔ peg0 G h ∧ peg0 G (seql t I))
Proof
  simp[seql_def, peg0_pegf]
QED

Theorem peg0_tokeq:
  peg0 G (tokeq t) = F
Proof
  simp[tokeq_def]
QED

Theorem peg0_tokSymP[simp]:
  peg0 G (tokSymP P) ⇔ F
Proof
  simp[tokSymP_def]
QED

Theorem peg0_tokIdP[simp]:
  peg0 G (tokIdP P) ⇔ F
Proof
  simp[tokIdP_def]
QED

Theorem peg0_choicel:
  (peg0 G (choicel []) = F) ∧
  (peg0 G (choicel (h::t)) ⇔ peg0 G h ∨ pegfail G h ∧ peg0 G (choicel t))
Proof
  simp[choicel_def]
QED

fun pegnt(t,acc) = let
  val th =
      Q.prove(`¬peg0 camlPEG (pnt ^t)`,
              simp pegnt_case_ths
              \\ simp [camlpeg_rules_applied]
              \\ simp [FDOM_camlPEG, pegf_def, seql_def, choicel_def,
                       tokPragma_def, peg_linfix_def, tokeq_def, try_def,
                       pegf_def]
              \\ simp (peg0_rwts @ acc))
  val nm = "peg0_" ^ term_to_string t
  val th' = save_thm(nm, SIMP_RULE bool_ss [pnt_def] th)
  val _ = export_rewrites [nm]
in
  th::acc
end

val npeg0_rwts =
    List.foldl pegnt []
      [ “nShiftOp”, “nMultOp”, “nAddOp”, “nRelOp”, “nAndOp”, “nOrOp”,
        “nHolInfixOp”, “nCatOp”, “nPrefixOp”, “nAssignOp”, “nValueName”,
        “nOperatorName”, “nConstrName”, “nTypeConstrName”, “nModuleName”,
        “nValuePath”, “nConstr”, “nTypeConstr”, “nModulePath”, “nFieldName”,
        “nUpdate”, “nUpdates”, “nERecUpdate”, “nERecCons”, “nLiteral”,
        “nIdent”, “nEList”, “nEConstr”, “nEBase”, “nEPrefix”, “nERecProj”,
        “nELazy”, “nEAssert”, “nEFunapp”, “nEApp”, “nLetBinding”, “nPAny”,
        “nPList”, “nPPar”, “nPBase”, “nPCons”, “nPAs”, “nPOps”, “nPattern”,
        “nPatterns”, “nLetBindings”, “nLetRecBinding”, “nLetRecBindings”,
        “nPatternMatches”, “nPatternMatch”, “nEMatch”, “nETry”, “nEFun”,
        “nEFunction”, “nELet”, “nELetRec”, “nEWhile”, “nEFor”, “nEUnclosed”,
        “nENeg”, “nEShift”, “nEMult”, “nEAdd”, “nECons”, “nECat”, “nERel”,
        “nEAnd”, “nEOr”, “nEHolInfix”, “nEProd”, “nEAssign”, “nEIf”, “nESeq”,
        “nExpr”, “nTypeDefinition”, “nTypeDef”, “nTypeDefs”, “nTVar”, “nTBase”,
        “nTConstr”, “nTProd”, “nTFun”, “nType”, “nTypeList”, “nTypeLists”,
        “nTypeParams”, “nConstrDecl”, “nTypeReprs”, “nTypeRepr”, “nTypeInfo”,
        “nConstrArgs”, “nExcDefinition”, “nTopLet”, “nTopLetRec”, “nOpen”,
        “nSemis”, “nExprItem”, “nExprItems”, “nModuleDef”, “nModTypeName”,
        “nModTypePath”, “nSigSpec”, “nExcType”, “nValType”, “nOpenMod”,
        “nIncludeMod”, “nModTypeAsc”, “nModTypeAssign”, “nSigItem”, “nSigItems”,
        “nModuleType”, “nModAscApp”, “nModAscApps”, “nCakeMLPragma”,
        “nModuleTypeDef”, “nDefinition”, “nDefItem”, “nModExpr”, “nModuleItem”
      ];

fun wfnt(t,acc) = let
  val th =
    Q.prove(`wfpeg camlPEG (pnt ^t)`,
          SIMP_TAC (srw_ss())
                   [camlpeg_rules_applied ,
                    wfpeg_pnt, FDOM_camlPEG, try_def,
                    choicel_def, seql_def, tokIdP_def, identMixed_def,
                    identLower_def, tokPragma_def,
                    tokeq_def, peg_linfix_def] THEN
          simp(wfpeg_rwts @ npeg0_rwts @ peg0_rwts @ acc))
in
  th::acc
end;

val topo_nts =
      [ “nShiftOp”, “nMultOp”, “nAddOp”, “nRelOp”, “nAndOp”, “nOrOp”,
        “nHolInfixOp”, “nCatOp”, “nPrefixOp”, “nAssignOp”, “nValueName”,
        “nOperatorName”, “nConstrName”, “nTypeConstrName”, “nModuleName”,
        “nModulePath”, “nValuePath”, “nConstr”, “nTypeConstr”, “nFieldName”,
        “nLiteral”, “nIdent”, “nEList”, “nEConstr”, “nERecUpdate”,
        “nERecCons”, “nEBase”, “nEPrefix”, “nERecProj”, “nELazy”, “nEAssert”,
        “nEFunapp”, “nEApp”, “nPAny”, “nPList”, “nPPar”, “nPBase”, “nPCons”,
        “nPAs”, “nPOps”, “nPattern”, “nPatterns”, “nLetBinding”, “nLetBindings”,
        “nLetRecBinding”, “nLetRecBindings”, “nPatternMatches”, “nPatternMatch”,
        “nEMatch”, “nETry”, “nEFun”, “nEFunction”, “nELet”, “nELetRec”,
        “nEWhile”, “nEFor”, “nEUnclosed”, “nENeg”, “nEShift”, “nEMult”, “nEAdd”,
        “nECons”, “nECat”, “nERel”, “nEAnd”, “nEOr”, “nEHolInfix”, “nEProd”,
        “nEAssign”, “nEIf”, “nESeq”, “nExpr”, “nTypeDefinition”, “nTVar”,
        “nTBase”, “nTConstr”, “nTProd”, “nTFun”, “nType”, “nTypeList”,
        “nTypeLists”, “nTypeParams”, “nTypeDef”, “nTypeDefs”, “nConstrDecl”,
        “nTypeReprs”, “nTypeRepr”, “nTypeInfo”, “nUpdate”, “nUpdates”,
        “nFieldDec”, “nFieldDecs”, “nRecord”, “nConstrArgs”, “nExcDefinition”,
        “nTopLet”, “nTopLetRec”, “nOpen”, “nSemis”, “nExprItem”, “nExprItems”,
        “nModuleDef”, “nModTypeName”, “nModTypePath”, “nSigSpec”, “nExcType”,
        “nValType”, “nOpenMod”, “nIncludeMod”, “nModTypeAsc”, “nModTypeAssign”,
        “nSigItem”, “nSigItems”, “nModuleType”, “nModAscApp”, “nModAscApps”,
        “nCakeMLPragma”, “nModuleTypeDef”, “nModExpr”, “nDefinition”,
        “nDefItem”, “nModuleItem”, “nModuleItems”, “nStart”];

val cml_wfpeg_thm = save_thm(
  "cml_wfpeg_thm",
  LIST_CONJ (List.foldl wfnt [] topo_nts))

val subexprs_pnt = Q.prove(
  `subexprs (pnt n) = {pnt n}`,
  simp [pegTheory.subexprs_def, pnt_def]);

Theorem PEG_exprs =
   “Gexprs camlPEG”
  |> SIMP_CONV (srw_ss())
       [pegTheory.Gexprs_def, pegTheory.subexprs_def, peg_range,
        try_def, tokeq_def, seql_def, pegf_def, choicel_def,
        sumID_def,
        subexprs_pnt, peg_start, INSERT_UNION_EQ ];

Theorem PEG_wellformed[simp]:
   wfG camlPEG
Proof
  simp [pegTheory.wfG_def, pegTheory.Gexprs_def, pegTheory.subexprs_def,
        subexprs_pnt, peg_start, peg_range, DISJ_IMP_THM, FORALL_AND_THM,
        choicel_def, seql_def, pegf_def, tokeq_def, try_def, tokPragma_def,
        peg_linfix_def, tokSymP_def, tokIdP_def]
  \\ simp (cml_wfpeg_thm :: wfpeg_rwts @ peg0_rwts @ npeg0_rwts)
QED

Theorem parse_Start_total =
  MATCH_MP pegexecTheory.peg_exec_total PEG_wellformed
  |> REWRITE_RULE [peg_start]
  |> Q.GEN `i`;

Theorem coreloop_Start_total =
  MATCH_MP pegexecTheory.coreloop_total PEG_wellformed
  |> REWRITE_RULE [peg_start]
  |> Q.GEN `i`;

Theorem owhile_Start_total =
  SIMP_RULE (srw_ss()) [pegexecTheory.coreloop_def] coreloop_Start_total;

val _ = export_theory ();

