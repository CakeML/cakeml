module Parse where
import Text.Parsec
import Text.Parsec.Prim
import Text.Parsec.Pos
import Data.List as List
import Data.Char as Char
import Tokens

o f g x = f (g x)

isTyvarT (TyvarT _) = True
isTyvarT _ = False

isLongidT (LongidT _ _) = True
isLongidT _ = False

isInt (IntT _) = True
isInt _ = False

isAlphaSym (AlphaT _) = True
isAlphaSym (SymbolT _) = True
isAlphaSym _ = False

destLongidT (LongidT x y) = Just (x,y)
destLongidT _ = Nothing

destAlphaT (AlphaT x) = Just x
destAlphaT _ = Nothing

destSymbolT (SymbolT x) = Just x
destSymbolT _ = Nothing

assert x =
  if x then Just () else Nothing

tok f = token show (\t -> initialPos "Unknown") (\t -> if f t then Just t else Nothing)

tokeq t = tok ((==) t)

seql = sequence

peg_nonfix tgtnt argsym opsym =
  seql [argsym, opsym, argsym]

peg_linfix exp op = exp `chainl1` op

rpt = many

peg_TypeDec =
  seq (tokeq DatatypeT) (nDtypeDecl `chainl1` tokeq AndT)

peg_longV = tok (\t -> (do (str,s) <- destLongidT t;
                           assert (s /= "" && (not (isAlpha (List.head s)) || not (isUpper (List.head s)))))
                       == Just ())

peg_UQConstructorName =
  tok (\t -> (do s <- destAlphaT t ;
                 assert (s /= "" && isUpper (List.head s) || s `elem` ["true", "false", "ref"]))
              == Just ())

peg_EbaseParen =
  seql [tokeq LparT, nE,
        choice [tokeq RparT,
                seql [tokeq CommaT, nElist1, tokeq RparT],
                seql [tokeq SemicolonT, nEseq, tokeq RparT]]]

peg_V =
   choice [tok (\t ->
                  (do s <- destAlphaT t;
                      assert(s `elem` ["before", "div", "mod", "o",
                                      "true", "false","ref"] &&
                            s /= "" && not (isUpper (List.head s))))
                  == Just ())
           tok (\t ->
                  (do s <- destSymbolT t;
                      assert(s `elem` ["+", "-", "/", "<", ">", "<=", ">=", "<>",
                                      ":=", "*"]))
                  == Just ())]

nV = peg_V

nTyvarN = tok isTyvarT

nVlist1 = seql [nV, try nVlist1]

nFQV = choice [nV, peg_longV]

nExn = choice [tokeq (AlphaT "Bind"),
               tokeq (AlphaT "Div"),
	       seql [tokeq (AlphaT "IntError"), tok isInt]]

nEapp = chainl1 [nEbase, rpt nEbase]

nElist1 = seql [nE, try (seql [tokeq CommaT, nElist1])]

nMultOps = choice (List.map tokeq [StarT, SymbolT "/", AlphaT "mod", AlphaT "div"])

nAddOps = choice [tokeq (SymbolT "+"), tokeq (SymbolT "-")]

nRelOps = choice (tok ((==) EqualsT) : List.map (tokeq `o` SymbolT) ["<", ">", "<=", ">=", "<>"])

nCompOps = choice [tokeq (SymbolT ":="), tokeq (AlphaT "o")]

nEbase = choice [tok isInt,
                 seql [tokeq LparT, tokeq RparT],
		 peg_EbaseParen,
		 seql [tokeq LetT, nLetDecs, tokeq InT, nEseq, tokeq EndT],
		 nFQV,
		 nConstructorName]

nEseq = seql [nE, try (seql [tokeq SemicolonT, nEseq])]

nEmult = peg_linfix nEapp nMultOps

nEadd = peg_linfix nEmult nAddOps

nErel = peg_nonfix nErel nEadd nRelOps

nEcomp = peg_linfix nErel nCompOps

nEbefore = peg_linfix nEcomp (tokeq (AlphaT "before"))

nEtyped = seql [nEbefore, try ([tokeq ColonT, nType])]

nElogicAND = peg_linfix nEtyped (tokeq AndalsoT)

nElogicOR = peg_linfix nElogicAND (tokeq OrelseT)

nEhandle = seql [nElogicOR,
                 try (seql [tokeq HandleT, tokeq (AlphaT "IntError"), nV,
                            tokeq DarrowT, nE])]

nEhandle' = seql [nElogicOR,
                  try (seql [tokeq HandleT, tokeq (AlphaT "IntError"), nV,
                             tokeq DarrowT, nE'])]

nE = choice [seql [tokeq RaiseT, nExn],
             nEhandle,
             seql [tokeq IfT, nE, tokeq ThenT, nE, tokeq ElseT, nE],
	     seql [tokeq FnT, nV, tokeq DarrowT, nE],
	     seql [tokeq CaseT, nE, tokeq OfT, nPEs]]

nE' = choice [seql [tokeq RaiseT, nExn],
              nEhandle',
              seql [tokeq IfT, nE, tokeq ThenT, nE,
                    tokeq ElseT, nE'],
              seql [tokeq FnT, nV, tokeq DarrowT, nE']]

nPEs = choice [seql [nPE', tokeq BarT, nPEs],
               nPE]

nPE = seql [nPattern, tokeq DarrowT, nE]

nPE' = seql [nPattern, tokeq DarrowT, nE']

nAndFDecls = peg_linfix nFDecl (tokeq AndT)

nFDecl = seql [nV, nVlist1, tokeq EqualsT, nE]

nType = seql [nPType, try (seql [tokeq ArrowT, nType])]

nDType = seql [nTbase, rpt nTyOp]

nTbase = choice [seql [tokeq LparT, nType, tokeq RparT],
                 seql [tokeq LparT, nTypeList2, tokeq RparT, nTyOp],
                 tok isTyvarT,
                 nTyOp]

nTypeList2 = seql [nType, tokeq CommaT, nTypeList1]

nTypeList1 = seql [nType, try (seql [tokeq CommaT, nTypeList1])]

nTyOp = choice [nUQTyOp, tok isLongidT]

nUQTyOp = tok isAlphaSym

nPType = seql [nDType, try (seql [tokeq StarT, nPType])]

nTypeName = choice [nUQTyOp,
                    seql [tokeq LparT, nTyVarList, tokeq RparT, nUQTyOp],
                    seql [tok isTyvarT, nUQTyOp]]

nTyVarList = peg_linfix nTyvarN (tokeq CommaT)

nTypeDec = peg_TypeDec

nDtypeDecl = seql [nTypeName, tokeq EqualsT,
                   peg_linfix nDconstructor (tokeq BarT)]

nDconstructor = seql [nUQConstructorName,
                      try (seql [tokeq OfT, nType])]

nUQConstructorName = peg_UQConstructorName

nConstructorName = choice [nUQConstructorName,
                           tok (\t -> (do (str,s) <- destLongidT t;
                                          assert (s /= "" && Char.isAlpha (List.head s) && Char.isUpper (List.head s)))
                                       == Just ())]

nPbase = choice [nV, nConstructorName, tok isInt,
                 nPtuple, tokeq UnderbarT]

nPattern = choice [seql [nConstructorName, nPbase], nPbase]

nPatternList = seql [nPattern,
                     try (seql [tokeq CommaT, nPatternList])]

nPtuple = choice [seql [tokeq LparT, tokeq RparT],
                  seql [tokeq LparT, nPatternList, tokeq RparT]]

nLetDec = choice [seql [tokeq ValT, nV, tokeq EqualsT, nE],
                  seql [tokeq FunT, nAndFDecls]]

nLetDecs = choice [seql [nLetDec, nLetDecs],
                   seql [tokeq SemicolonT, nLetDecs]]

nDecl = choice [seql [tokeq ValT, nPattern, tokeq EqualsT, nE],
                seql [tokeq FunT, nAndFDecls],
		seql [nTypeDec]]

nDecls = choice [seql [nDecl, nDecls],
                 seql [tokeq SemicolonT, nDecls]]

nSpecLine = choice [seql [tokeq ValT, nV, tokeq ColonT, nType],
                    seql [tokeq TypeT, nTypeName],
                    nTypeDec]

nSpecLineList = choice [seql [nSpecLine, nSpecLineList],
                        seql [tokeq SemicolonT, nSpecLineList]]

nSignatureValue = seql [tokeq SigT, nSpecLineList, tokeq EndT]

nOptionalSignatureAscription = try (seql [tokeq SealT, nSignatureValue])

nStructure = seql [tokeq StructureT, nV, nOptionalSignatureAscription,
                   tokeq EqualsT, tokeq StructT, nDecls, tokeq EndT]

nTopLevelDec = choice [nStructure, nDecl]

nREPLTop = choice [seql [nE, tokeq SemicolonT],
                   seql [nTopLevelDec, tokeq SemicolonT]]
