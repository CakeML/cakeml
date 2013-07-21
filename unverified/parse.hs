module Parse where
import Control.Monad
import Text.Parsec
import Text.Parsec.Prim
import Text.Parsec.Pos
import Data.List as List
import Data.Char as Char
import Tokens
import Ast
import Data.Maybe

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

destIntT (IntT i) = Just i
destIntT _ = Nothing

destTyvarT (TyvarT tv) = Just tv
destTyvarT _ = Nothing

tok :: (Token -> Maybe a) -> Parsec [Token] u a
tok f = token show (\t -> initialPos "Unknown") (\t -> f t)

tokeq t = tok (\x -> if t == x then Just x else Nothing)

linfix exp op = exp `chainl1` fmap (\t e1 e2 -> Ast_App (Ast_App (Ast_Var t) e1) e2) op

rpt = many

peg_longV = tok (\t -> do (str,s) <- destLongidT t;
                          guard (s /= "" && (not (isAlpha (List.head s)) || not (isUpper (List.head s))));
                          return (str,s))
nV =
  choice [tok (\t -> do s <- destAlphaT t; 
			guard (not (s `elem` ["before", "div", "mod", "o", "true", "false","ref"]) && 
                               s /= "" && 
			       not (isUpper (List.head s)));
			return s),
          tok (\t -> do s <- destSymbolT t;
		        guard (s `elem` ["+", "-", "/", "<", ">", "<=", ">=", "<>", ":=", "*"]);
	                return s)]

nTyvarN = do t <- destTyvarT;
             return t

nVlist1 = many1 nV

-- nFQV = choice [nV, peg_longV]

nExn = choice [tokeq (AlphaT "Bind") >> return Bind_error,
               tokeq (AlphaT "Div") >> return Div_error,
	       do tokeq (AlphaT "IntError");
                  i <- tok destIntT;
                  return (Int_error i)]

mkAst_App e1 e2 =
  case e1 of
    Ast_Con (Just (Short "ref")) [] -> Ast_App (Ast_Var (Short "ref")) e2
    Ast_Con s [] ->
      case e2 of
        Ast_Con Nothing es -> Ast_Con s es
        _ -> Ast_Con s [e2]
    _ -> Ast_App e1 e2

nEapp = do exps <- many1 nEbase;
           return (case exps of
	             [e] -> e
		     (e:es) -> List.foldl mkAst_App e es)

nElist1 = sepBy1 nE CommaT

nMultOps = choice [tokeq StarT >> return "*", 
                   tokeq (SymbolT "/") >> return "/", 
		   tokeq (AlphaT "mod") >> return "mod", 
		   tokeq (AlphaT "div") >> return "div"]

nAddOps = choice [tokeq (SymbolT "+") >> return "+", tokeq (SymbolT "-") >> return "-"]

nRelOps = choice ((tokeq EqualsT >> return "=") : List.map (\s -> tokeq (SymbolT s) >> return s) ["<", ">", "<=", ">=", "<>"])

nCompOps = choice [tokeq (SymbolT ":=") >> return ":=", tokeq (AlphaT "o") >> return "o"]

eseq_encode [] = Ast_Lit Unit
eseq_encode [e] = [e]
eseq_encode (e:es) = Ast_Let "_" e (eseq_encode es)

peg_EbaseParen =
  do tokeq LparT;
     choice [tokeq RparT >> return (Ast_Lit Unit),
             do e1 <- nE;
                choice [tokeq RparT >> return e1,
		        do tokeq CommaT;
                           es <- nElist1;
			   tokeq RparT;
                           return (Ast_Con Nothing (e1:es)),
                        do tokeq SemicolonT;
 		           es <- nEseq;
			   tokeq RparT;
			   return (eseq_encode (e1:es))]]


nEbase = choice [do i <- tok destIntT;
                    return (Ast_Lit (IntLit i)),
		 peg_EbaseParen,
		 do tokeq LetT;
                    lets <- nLetDecs;
                    tokeq InT;
                    es <- nEseq;
                    tokeq EndT,
		 nFQV,
		 nConstructorName]

nEseq = sepBy1 nE (tokeq SemicolonT)

nEmult = linfix nEapp nMultOps

nEadd = linfix nEmult nAddOps

nErel = 
  do e1 <- nEadd;
     op <- nRelOps;
     e2 <- nEadd;
     return (Ast_App (Ast_App (Ast_Var op) e1) e2)

nEcomp = linfix nErel nCompOps

nEbefore = linfix nEcomp (tokeq (AlphaT "before"))

nEtyped = 
  do e <- nEbefore;
     t <- try (do tokeq ColonT;
                  nType)
     return e

nElogicAND = nEtyped `chainl1` (tokeq AndalsoT >> return (\e1 e2 -> Ast_Log And e1 e2))

nElogicOR = nElogicAND `chainl1` (tokeq OrelseT >> return (\e1 e2 -> Ast_Log Or e1 e2))

nEhandle = 
  do e1 <- nElogicOR;
     tokeq HandleT;
     tokeq (AlphaT "IntError");
     v <- nV;
     tokeq DarrowT;
     e2 <- nE;
     return (Ast_Handle e1 v e2)

nEhandle' = 
  do e1 <- nElogicOR;
     tokeq HandleT;
     tokeq (AlphaT "IntError");
     v <- nV;
     tokeq DarrowT;
     e2 <- nE';
     return (Ast_Handle e1 v e2)

nE = choice [tokeq RaiseT >> nExn,
             try nEhandle,
	     nElogicOR,
             do tokeq IfT;
                e1 <- nE;
		tokeq ThenT;
		e2 <- nE;
		tokeq ElseT;
		e3 <- nE;
 		return (Ast_If e1 e2 e3),
	     do tokeq FnT;
                x <- nV;
		tokeq DarrowT;
		e <- nE;
		return (Ast_Fun x e),
	     do tokeq CaseT;
                e <- nE; 
		tokeq OfT;
		pes <- nPEs;
		return (Ast_Mat e pes)]

nE' = choice [tokeq RaiseT >> nExn,
              try nEhandle',
	      nElogicOR,
              do tokeq IfT;
                 e1 <- nE;
		 tokeq ThenT;
		 e2 <- nE;
		 tokeq ElseT;
		 e3 <- nE';
		 return (Ast_If e1 e2 e3),
 	      do tokeq FnT;
                 x <- nV;
		 tokeq DarrowT;
		 e <- nE';
		 return (Ast_Fun x e)]


nPEs = choice [try (do pe <- nPE'; tokeq BarT; pes <- nPEs; return (pe:pes)),
               fmap (\x -> [x]) nPE]

nPE = do p <- nPattern;
         tokeq DarrowT;
	 e <- nE;
         return (p,e)

nPE' = do p <- nPattern;
          tokeq DarrowT;
 	  e <- nE';
          return (p,e)


{-
nAndFDecls = nFDecl `chainl1` (tokeq AndT >> (\d1 d2 -> ))

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

nTypeDec = seq (tokeq DatatypeT) (nDtypeDecl `chainl1` tokeq AndT)

nDtypeDecl = seql [nTypeName, tokeq EqualsT,
                   peg_linfix nDconstructor (tokeq BarT)]

nDconstructor = seql [nUQConstructorName,
                      try (seql [tokeq OfT, nType])]
-}

nUQConstructorName = 
  tok (\t -> do s <- destAlphaT t; 
                guard (s /= "" && isUpper (List.head s) || s `elem` ["true", "false", "ref"]);
                return (Short s))

nConstructorName = 
  choice [nUQConstructorName,
          tok (\t -> do (str,s) <- destLongidT t;
                        guard (s /= "" && Char.isAlpha (List.head s) && Char.isUpper (List.head s));
			return (Long str s))]

mk_pat_app n p =
  if n == Short "ref" then Ast_Pref p
  else 
    case p of 
      Ast_Pcon Nothing ps -> Ast_Pcon (Just n) ps
      _ -> Ast_Pcon (Just n) [p]

-- TODO: negative numbers
-- TODO: underscore patterns
nPbase = choice [fmap Ast_Pvar nV, 
                 do n <- nConstructorName;
                    return (if n == Short "true" then Ast_Plit (Bool True)
		            else if n == Short "false" then Ast_Plit (Bool False) 
			    else Ast_Pcon (Just n) []),
                 do i <- tok destIntT;
		    return (Ast_Plit (IntLit i)),
                 nPtuple, 
                 tokeq UnderbarT >> return (Ast_Pvar "_")]

nPattern = choice [try (do n <- nConstructorName;
                           pat <- nPbase;
                           return (mk_pat_app n pat)), 
                   nPbase]

nPtuple = 
  tokeq LparT >>
  choice [tokeq RparT >> return (Ast_Plit Unit),
          do pats <- sepBy1 nPattern (tokeq CommaT);
             tokeq RparT;
	     return (Ast_Pcon Nothing pats)]

{-
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
-}
