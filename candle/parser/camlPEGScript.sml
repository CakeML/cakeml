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
 *)

Definition identUpperLower_def:
  identUpperLower s ⇔
    s ≠ "" ∧
    isUpper (HD s) ∧
    ¬NULL (TL s) ∧
    idChar isLower (TL s)
End

(* Names of values according to HOL light are all combinations of identifier
 * characters (alphanumerics, underscore and tick) _except_ those that are
 * module names or type constructors: if the name starts with an uppercase
 * letter then the rest must contain at least one uppercase letter.
 *)

Definition identMixed_def:
  identMixed s ⇔
    s ≠ "" ∧
    idChar isAlpha (TL s) ∧
    ((isLower (HD s) ∨ HD s = #"_") ∨
     (isUpper (HD s) ∧ ¬NULL (TL s) ⇒ EXISTS isUpper (TL s)))
End


Datatype:
  camlNT =
    (* hol-light specific operators *)
    | nEHolInfix | nHolInfixOp
    (* different sorts of names *)
    | nValueName | nOperatorName | nConstrName | nTypeConstrName | nModuleName
    | nValuePath | nConstr | nTypeConstr | nModulePath
    (* expressions *)
    | nLiteral | nIdent | nEBase | nEList
    | nEApp | nEConstr | nEFunapp | nEAssert | nELazy
    | nEPrefix | nENeg | nEShift | nEMult
    | nEAdd | nECons | nECat | nERel
    | nEAnd | nEOr | nEProd | nEIf | nESeq
    | nEMatch | nETry | nEFun | nEFunction | nELet | nELetRec
    | nEWhile | nEFor | nExpr
    (* pattern matches *)
    | nLetBinding | nLetBindings | nLetRecBinding | nLetRecBindings
    | nPatternMatch | nPatternMatches
    (* type definitions *)
    | nTypeDefinition | nTypeDef | nTypeDefs | nTypeParams | nTypeInfo
    | nTypeRepr | nTypeReprs | nConstrDecl | nConstrArgs | nExcDefinition
    (* patterns *)
    | nPAny | nPBase | nPLazy | nPConstr | nPApp | nPCons | nPProd
    | nPOr | nPAs | nPList | nPattern | nPatterns
    (* types *)
    | nTypeList | nTypeLists
    | nTVar | nTAny | nTBase | nTConstr | nTProd | nTFun
    | nTAs | nType
    (* definitions *)
    | nDefinition | nTopLet | nTopLetRec | nModuleItem | nModuleItems | nOpen
    | nModExpr | nModuleDef
    | nSemis | nExprItem | nExprItems | nDefItem
    (* misc *)
    | nShiftOp | nMultOp | nAddOp | nRelOp | nAndOp | nOrOp
    | nStart
End

(* Printing names of non-terminals, useful for debugging the parse-tree
 * to ast conversion.
 *)

Definition camlNT2string_def:
  camlNT2string n =
    case n of
      nEHolInfix => strlit"hol-infix-expression"
    | nHolInfixOp => strlit"hol-infix-op"
    | nValueName => strlit"value-name"
    | nOperatorName => strlit"operator-name"
    | nConstrName => strlit"constr-name"
    | nTypeConstrName => strlit"typeconstr-name"
    | nModuleName => strlit"module-name"
    | nValuePath => strlit"value-path"
    | nConstr => strlit"constr"
    | nTypeConstr => strlit"typeconstr"
    | nModulePath => strlit"module-path"
    | nLiteral => strlit"literal"
    | nIdent => strlit"ident"
    | nEBase => strlit"base-expr"
    | nEList => strlit"list-expr"
    | nEApp => strlit"app-expr"
    | nEConstr => strlit"constr-app"
    | nEFunapp => strlit"fun-app"
    | nEAssert => strlit"assert-app"
    | nELazy => strlit"lazy-app"
    | nEPrefix => strlit"prefix-op"
    | nENeg => strlit"negation-op"
    | nEShift => strlit"shift-op"
    | nEMult => strlit"mult-op"
    | nEAdd => strlit"add-op"
    | nECons => strlit"cons-op"
    | nECat => strlit"cat-op"
    | nERel => strlit"rel-op"
    | nEAnd => strlit"and-op"
    | nEOr => strlit"or-op"
    | nEProd => strlit"prod-op"
    | nEIf => strlit"if-then[-else]"
    | nESeq => strlit"seq (;)"
    | nEMatch => strlit"match"
    | nETry => strlit"try"
    | nEFun => strlit"fun"
    | nEFunction => strlit"function"
    | nELet => strlit"let"
    | nELetRec => strlit"let rec"
    | nEWhile => strlit"while"
    | nEFor => strlit"for"
    | nExpr => strlit"expr"
    | nLetBinding => strlit"let-binding"
    | nLetBindings => strlit"let-bindings"
    | nLetRecBinding => strlit"letrec-binding"
    | nLetRecBindings => strlit"letrec-bindings"
    | nPatternMatch => strlit"pattern-match"
    | nPatternMatches => strlit"pattern-matches"
    | nTypeDefinition => strlit"type-definition"
    | nTypeDef => strlit"type-def"
    | nTypeDefs => strlit"type-defs"
    | nTypeParams => strlit"type-params"
    | nTypeInfo => strlit"type-info"
    | nTypeRepr => strlit"type-repr"
    | nTypeReprs => strlit"type-reprs"
    | nConstrDecl => strlit"constr-decl"
    | nConstrArgs => strlit"constr-args"
    | nExcDefinition => strlit"exc-definition"
    | nPAny => strlit"pat-any"
    | nPBase => strlit"pat-base"
    | nPLazy => strlit"pat-lazy"
    | nPConstr => strlit"pat-constr"
    | nPApp => strlit"pat-app"
    | nPCons => strlit"pat-cons"
    | nPProd => strlit"pat-prod"
    | nPOr => strlit"pat-or"
    | nPAs => strlit"pat-as"
    | nPList => strlit"pat-list"
    | nPattern => strlit"pattern"
    | nPatterns => strlit"patterns"
    | nTypeList => strlit"type-list"
    | nTypeLists => strlit"type-lists"
    | nTVar => strlit"type-var"
    | nTAny => strlit"type-any"
    | nTBase => strlit"type-base"
    | nTConstr => strlit"type-constr"
    | nTProd => strlit"type-prod"
    | nTFun => strlit"type-fun"
    | nTAs => strlit"type-as"
    | nType => strlit"type"
    | nDefinition => strlit"definition"
    | nTopLet => strlit"top-let"
    | nTopLetRec => strlit"top-letrec"
    | nModuleItem => strlit"module-item"
    | nModuleItems => strlit"module-items"
    | nOpen => strlit"open"
    | nModExpr => strlit"mod-expr"
    | nModuleDef => strlit"module-def"
    | nShiftOp => strlit"shift-op"
    | nMultOp => strlit"mult-op"
    | nAddOp => strlit"add-op"
    | nRelOp => strlit"rel-op"
    | nAndOp => strlit"and-op"
    | nOrOp => strlit"or-op"
    | nStart => strlit"start"
    | nSemis => strlit"double-semicolons"
    | nExprItem => strlit"expr-item"
    | nExprItems => strlit"expr-items"
    | nDefItem => strlit"def-item"
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
                      tokSymP validPrefixSym;
                      tokSymP validCatOp ])
            (bindNT nOperatorName));
      (INL nConstrName,
       pegf (tokIdP identUpperLower) (bindNT nConstrName));
      (INL nTypeConstrName,
       pegf (tokIdP identMixed) (bindNT nTypeConstrName));
      (INL nModuleName,
       pegf (tokIdP identUpperLower) (bindNT nModuleName));
      (INL nValuePath,
       seql [try (seql [pnt nModulePath; tokeq DotT] I); pnt nValueName]
            (bindNT nValuePath));
      (INL nConstr,
       seql [try (seql [pnt nModulePath; tokeq DotT] I); pnt nConstrName]
            (bindNT nConstr));
      (INL nTypeConstr,
       seql [try (seql [pnt nModulePath; tokeq DotT] I); pnt nTypeConstrName]
            (bindNT nTypeConstr));
      (INL nModulePath,
       seql [pnt nModuleName; try (seql [tokeq DotT; pnt nModulePath] I)]
            (bindNT nModulePath));
      (* -- Definitions ---------------------------------------------------- *)
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
                      seql [tokeq StructT; pnt nModuleItems; tokeq EndT] I])
            (bindNT nModExpr));
      (INL nModuleDef,
       seql [tokeq ModuleT; pnt nModuleName; tokeq EqualT; pnt nModExpr]
            (bindNT nModuleDef));
      (INL nDefinition,
       pegf (choicel [pnt nTopLetRec;
                      pnt nTopLet;
                      pnt nTypeDefinition;
                      pnt nExcDefinition;
                      pnt nOpen;
                      pnt nModuleDef;
                      (* module type *)
                      (* include moduleexpr *)
                      ])
            (bindNT nDefinition));
      (* -- Typedef -------------------------------------------------------- *)
      (INL nExcDefinition,
       seql [tokeq ExceptionT;
             choicel [pnt nConstrDecl;
                      seql [pnt nConstrName; tokeq EqualT; pnt nConstr] I]]
            (bindNT nExcDefinition));
      (INL nTypeDefinition,
       seql [tokeq TypeT; try (tokeq NonrecT); pnt nTypeDefs]
            (bindNT nTypeDefinition));
      (INL nTypeDef,
       seql [try (pnt nTypeParams); pnt nTypeConstrName; pnt nTypeInfo]
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
       choicel [seql [tokeq EqualT; pnt nType] (bindNT nTypeInfo);
                pegf (pnt nTypeRepr) (bindNT nTypeInfo)]);
      (INL nTypeRepr,
       seql [try (tokeq BarT); pnt nConstrDecl; try (pnt nTypeReprs)]
            (bindNT nTypeRepr));
      (INL nTypeReprs,
       seql [tokeq BarT; pnt nConstrDecl; try (pnt nTypeReprs)]
            (bindNT nTypeReprs));
      (INL nConstrDecl,
       seql [pnt nConstrName; try (seql [tokeq OfT; pnt nConstrArgs] I)]
            (bindNT nConstrDecl));
      (INL nConstrArgs,
       seql [pnt nType; rpt (seql [tokeq StarT; pnt nType] I) FLAT]
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
      (INL nTAny,
       pegf (tokeq AnyT) (bindNT nTAny));
      (INL nTBase,
       pegf (choicel [seql [tokeq LparT; pnt nType; tokeq RparT] I;
                      seql [tokeq LparT; pnt nTypeList; tokeq RparT;
                            pnt nTypeConstr] I;
                      pnt nTVar;
                      pnt nTAny])
            (bindNT nTBase));
      (* -- Type4 ---------------------------------------------------------- *)
      (INL nTConstr,
       seql [pnt nTBase; rpt (pnt nTypeConstr) FLAT]
            (bindNT nTConstr));
      (* -- Type3 ---------------------------------------------------------- *)
      (INL nTProd,
       seql [pnt nTConstr; try (seql [tokeq StarT; pnt nTProd] I)]
            (bindNT nTProd));
      (* -- Type2 ---------------------------------------------------------- *)
      (INL nTFun,
       seql [pnt nTProd; try (seql [tokeq RarrowT; pnt nTFun] I)]
            (bindNT nTFun));
      (* -- Type1 ---------------------------------------------------------- *)
      (INL nTAs,
       seql [pnt nTFun; try (seql [tokeq AsT; tokeq TickT; pnt nIdent] I)]
            (bindNT nTAs));
      (* -- Type ----------------------------------------------------------- *)
      (INL nType,
       pegf (pnt nTAs) (bindNT nType));
      (* -- Expr16 --------------------------------------------------------- *)
      (INL nEList,
       seql [tokeq LbrackT;
             try (seql [pnt nEIf;
                        try (rpt (seql [tokeq SemiT; pnt nEIf] I) FLAT);
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
      (INL nEBase,
       choicel [
         pegf (pnt nLiteral) (bindNT nEBase);
         pegf (pnt nValuePath) (bindNT nEBase);
         pegf (pnt nConstr) (bindNT nEBase);
         pegf (pnt nEList) (bindNT nEBase);
         seql [tokeq LparT; tokeq RparT] (bindNT nEBase); (* unit *)
         seql [tokeq BeginT; tokeq EndT] (bindNT nEBase); (* unit *)
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
       seql [pnt nConstr; pnt nEBase] (bindNT nEConstr));
      (INL nEFunapp,
       seql [pnt nEBase; rpt (pnt nEBase) FLAT]
            (λl. case l of
                   [] => []
                 | h::t => [FOLDL (λa b. mkNd (INL nEFunapp) [a; b])
                                  (mkNd (INL nEFunapp) [h]) t]));
      (INL nEApp,
       pegf (choicel (MAP pnt [nELazy; nEAssert; nEConstr; nEFunapp; nEBase]))
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
       pegf (choicel [tokeq PlusT; tokeq MinusT; tokeq MinusFT;
                      tokSymP validAddOp])
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
      (* -- Expr 4.5 ------------------------------------------------------- *)
      (INL nEHolInfix,
       peg_linfix (INL nEHolInfix) (pnt nEOr) (pnt nHolInfixOp));
      (* -- Expr4 ---------------------------------------------------------- *)
      (INL nEProd,
       seql [pnt nEHolInfix;
             try (rpt (seql [tokeq CommaT; pnt nEHolInfix] I) FLAT)]
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
       seql [pnt nEIf; try (seql [tokeq SemiT; pnt nESeq] I)]
            (bindNT nESeq));
      (* -- Expr0 ---------------------------------------------------------- *)
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
      (* -- Expr: everything else  ----------------------------------------- *)
      (INL nEWhile,
       seql [tokeq WhileT; pnt nExpr; tokeq DoT; pnt nExpr; tokeq DoneT]
            (bindNT nEWhile));
      (INL nEFor,
       seql [tokeq ForT; pnt nValueName; tokeq EqualT; pnt nExpr;
             choicel [tokeq ToT; tokeq DowntoT]; pnt nExpr;
             tokeq DoT; pnt nExpr; tokeq DoneT]
            (bindNT nEFor));
      (INL nExpr,
       pegf (choicel [
               (* e1: *)
               pnt nESeq;
               (* e0: *)
               pnt nELetRec; pnt nELet; pnt nEMatch; pnt nEFun; pnt nEFunction;
               pnt nETry;
               (* everything else: *)
               pnt nEWhile; pnt nEFor])
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
      (* -- Pat8 ----------------------------------------------------------- *)
      (INL nPList,
       seql [tokeq LbrackT;
             try (seql [pnt nPattern;
                        try (rpt (seql [tokeq SemiT; pnt nPattern] I) FLAT);
                        try (tokeq SemiT)] I);
             tokeq RbrackT]
            (bindNT nPList));
      (INL nPAny,
       pegf (tokeq AnyT) (bindNT nPAny));
      (INL nPBase,
       pegf (choicel [pnt nValueName;
                      pnt nPAny;
                      pnt nPList;
                      seql [tokeq LparT; tokeq RparT] I;
                      seql [tokeq LparT; pnt nPattern;
                            try (seql [tokeq ColonT; pnt nType] I);
                            tokeq RparT] I;
                      seql [tok isChar (bindNT nLiteral o mktokLf);
                            tokeq DotsT;
                            tok isChar (bindNT nLiteral o mktokLf)] I])
            (bindNT nPBase));
      (* -- Pat7 ----------------------------------------------------------- *)
      (INL nPLazy,
       seql [try (tokeq LazyT); pnt nPBase]
            (bindNT nPLazy));
      (* -- Pat6 ----------------------------------------------------------- *)
      (INL nPConstr,
       pegf (choicel [seql [pnt nConstr; try (pnt nPLazy)] I;
                      pnt nPLazy])
            (bindNT nPConstr));
      (INL nPApp,
       pegf (choicel [pnt nPConstr; pnt nPLazy])
            (bindNT nPApp));
      (* -- Pat5 ----------------------------------------------------------- *)
      (INL nPCons,
       seql [pnt nPApp; try (seql [tokeq ColonsT; pnt nPCons] I)]
            (bindNT nPCons));
      (* -- Pat4 ----------------------------------------------------------- *)
      (INL nPProd,
       seql [pnt nPCons; try (rpt (seql [tokeq CommaT; pnt nPCons] I) FLAT)]
            (bindNT nPProd));
      (* -- Pat3 ----------------------------------------------------------- *)
      (INL nPOr,
       peg_linfix (INL nPOr) (pnt nPProd) (tokeq BarT));
      (* -- Pat2 ----------------------------------------------------------- *)
      (INL nPAs,
       seql [pnt nPOr; try (seql [tokeq AsT; pnt nIdent] I)]
            (bindNT nPAs));
      (* -- Pat1 ----------------------------------------------------------- *)
      (INL nPattern,
       pegf (pnt nPAs) (bindNT nPattern));
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

val t1 = rhs $ concl $ time EVAL “lexer_fun "[] -> []"”;
val t2 = time EVAL “camlpegexec nPatternMatch ^t1”;

 *)

val _ = export_theory ();

