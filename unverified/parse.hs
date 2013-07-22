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

destLongidT (LongidT x y) = Just (x,y)
destLongidT _ = Nothing

destAlphaT (AlphaT x) = Just x
destAlphaT _ = Nothing

destSymbolT (SymbolT x) = Just x
destSymbolT _ = Nothing

destAlphaSym (AlphaT x) = Just x
destAlphaSym (SymbolT x) = Just x
destAlphaSym _ = Nothing

destIntT (IntT i) = Just i
destIntT _ = Nothing

destTyvarT (TyvarT tv) = Just tv
destTyvarT _ = Nothing

tok :: (Token -> Maybe a) -> Parsec [Token] u a
tok f = token show (\t -> initialPos "Unknown") (\t -> f t)

tokeq t = tok (\x -> if t == x then Just x else Nothing)

linfix exp op = exp `chainl1` fmap (\t e1 e2 -> Ast_App (Ast_App (Ast_Var (Short t)) e1) e2) op

rpt = many

peg_longV = tok (\t -> do (str,s) <- destLongidT t;
                          guard (s /= "" && (not (isAlpha (List.head s)) || not (isUpper (List.head s))));
                          return (str,s))
nV =
  tok (\t -> do s <- destAlphaT t; 
                guard (not (s `elem` ["before", "div", "mod", "o", "true", "false","ref"]) && 
                       s /= "" && 
		       not (isUpper (List.head s)));
		return s)
  <|>
  tok (\t -> do s <- destSymbolT t;
                guard (s `elem` ["+", "-", "/", "<", ">", "<=", ">=", "<>", ":=", "*"]);
		return s)

nVlist1 = many1 nV

nFQV = 
  fmap Short nV 
  <|> 
  fmap (\(x,y) -> Long x y) peg_longV

nExn = 
  (tokeq (AlphaT "Bind") >> return Bind_error)
  <|>
  (tokeq (AlphaT "Div") >> return Div_error)
  <|>
  do tokeq (AlphaT "IntError");
     i <- tok destIntT;
     return (Int_error i)

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

nElist1 = sepBy1 nE (tokeq CommaT)

nMultOps = 
  (tokeq StarT >> return "*")
  <|>
  (tokeq (SymbolT "/") >> return "/")
  <|> 
  (tokeq (AlphaT "mod") >> return "mod")
  <|>
  (tokeq (AlphaT "div") >> return "div")

nAddOps = 
  (tokeq (SymbolT "+") >> return "+")
  <|>
  (tokeq (SymbolT "-") >> return "-")

nRelOps = choice ((tokeq EqualsT >> return "=") : List.map (\s -> tokeq (SymbolT s) >> return s) ["<", ">", "<=", ">=", "<>"])

nCompOps = 
  (tokeq (SymbolT ":=") >> return ":=")
  <|>
  (tokeq (AlphaT "o") >> return "o")

eseq_encode [] = Ast_Lit Unit
eseq_encode [e] = e
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


do_let_dec (Left (x,e1)) e2 = Ast_Let x e1 e2
do_let_dec (Right funs) e = Ast_Letrec funs e

nEbase = 
  do i <- tok destIntT;
     return (Ast_Lit (IntLit i))
  <|>
  peg_EbaseParen
  <|>
  do tokeq LetT;
     lets <- nLetDecs;
     tokeq InT;
     es <- nEseq;
     tokeq EndT;
     return (List.foldr do_let_dec (eseq_encode es) lets)
  <|>
  fmap Ast_Var nFQV
  <|>
  do n <- nConstructorName;
     return (if n == Short "true" then Ast_Lit (Bool True)
	     else if n == Short "false" then Ast_Lit (Bool False) 
	     else Ast_Con (Just n) [])

nEseq = sepBy1 nE (tokeq SemicolonT)

nEmult = linfix nEapp nMultOps

nEadd = linfix nEmult nAddOps

nErel = 
  do e1 <- nEadd;
     op <- nRelOps;
     e2 <- nEadd;
     return (Ast_App (Ast_App (Ast_Var (Short op)) e1) e2)

nEcomp = linfix nErel nCompOps

nEbefore = linfix nEcomp (tokeq (AlphaT "before") >> return "before")

nEtyped = 
  do e <- nEbefore;
     t <- try (do tokeq ColonT;
                  nType)
     return e

nElogicAND = nEtyped `chainl1` (tokeq AndalsoT >> return (\e1 e2 -> Ast_Log And e1 e2))

nElogicOR = nElogicAND `chainl1` (tokeq OrelseT >> return (\e1 e2 -> Ast_Log Or e1 e2))

nEhandle = 
  do e1 <- nElogicOR;
     choice [do tokeq HandleT;
                tokeq (AlphaT "IntError");
	        v <- nV;
	        tokeq DarrowT;
	        e2 <- nE;
                return (Ast_Handle e1 v e2),
             return e1]

nEhandle' = 
  do e1 <- nElogicOR;
     choice [do tokeq HandleT;
                tokeq (AlphaT "IntError");
	        v <- nV;
	        tokeq DarrowT;
	        e2 <- nE';
                return (Ast_Handle e1 v e2),
             return e1]

nE = 
  (tokeq RaiseT >> fmap Ast_Raise nExn)
  <|>
  nEhandle
  <|>
  do tokeq IfT;
     e1 <- nE;
     tokeq ThenT;
     e2 <- nE;
     tokeq ElseT;
     e3 <- nE;
     return (Ast_If e1 e2 e3)
  <|>
  do tokeq FnT;
     x <- nV;
     tokeq DarrowT;
     e <- nE;
     return (Ast_Fun x e)
  <|>
  do tokeq CaseT;
     e <- nE; 
     tokeq OfT;
     pes <- nPEs;
     return (Ast_Mat e pes)

nE' = 
  (tokeq RaiseT >> fmap Ast_Raise nExn)
  <|>
  nEhandle'
  <|>
  do tokeq IfT;
     e1 <- nE;
     tokeq ThenT;
     e2 <- nE;
     tokeq ElseT;
     e3 <- nE';
     return (Ast_If e1 e2 e3)
  <|>
  do tokeq FnT;
     x <- nV;
     tokeq DarrowT;
     e <- nE';
     return (Ast_Fun x e)

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


nAndFDecls = sepBy1 nFDecl (tokeq AndT)

multi_funs x [y] e = (x,y,e)
multi_funs x (y:ys) e = (x,y,List.foldr Ast_Fun e ys)

nFDecl = do x <- nV;
            ys <- nVlist1;
            tokeq EqualsT;
            e <- nE;
            return (multi_funs x ys e)

nType = nPType `chainl1` (tokeq ArrowT >> return Ast_Tfn)

nDType = do t <- nTbase; 
            ts <- many nTyOp; 
            return (List.foldr (\tc t -> Ast_Tapp [t] (Just tc)) t ts)

nTbase = choice [tokeq LparT >> choice [do t <- nType; tokeq RparT; return t,
                                        do ts <- nTypeList2; 
                                           tokeq RparT; 
					   tc <- nTyOp; 
					   return (Ast_Tapp ts (Just tc))],
                 fmap Ast_Tvar (tok destTyvarT),
                 do tc <- nTyOp; return (Ast_Tapp [] (Just tc))]

nTypeList2 = do t <- nType;
                tokeq CommaT;
                ts <- nTypeList1;
                return (t:ts)

nTypeList1 = sepBy1 nType (tokeq CommaT)

nTyOp = fmap Short nUQTyOp <|> fmap (\(x,y) -> Long x y) (tok destLongidT)

nUQTyOp = tok destAlphaSym

nPType = fmap tuplify (sepBy1 nDType (tokeq StarT))

tuplify [ty] = ty
tuplify tys = Ast_Tapp tys Nothing

nTypeName = 
  fmap (\n -> (n,[])) nUQTyOp
  <|>
  do tokeq LparT;
     tvs <- nTyVarList;
     tokeq RparT;
     n <- nUQTyOp;
     return (n, tvs)
  <|>
  do tv <- tok destTyvarT;
     n <- nUQTyOp;
     return (n, [tv])

nTyVarList = sepBy1 (tok destTyvarT) (tokeq CommaT)

nTypeDec = 
  tokeq DatatypeT >> sepBy1 nDtypeDecl (tokeq AndT)

nDtypeDecl = 
  do (tn,tvs) <- nTypeName; 
     tokeq EqualsT;
     ctors <- sepBy1 nDconstructor (tokeq BarT);
     return (tvs,tn,ctors)

detuplify (Ast_Tapp args Nothing) = args
detuplify ty = [ty]

nDconstructor = 
  do cn <- nUQConstructorName;
     option (cn,[])
            (do tokeq OfT;
                t <- nType;
                return (cn, detuplify t))

nUQConstructorName = 
  tok (\t -> do s <- destAlphaT t; 
                guard (s /= "" && isUpper (List.head s) || s `elem` ["true", "false", "ref"]);
                return s)

nConstructorName = 
  fmap Short nUQConstructorName
  <|>
  tok (\t -> do (str,s) <- destLongidT t;
                guard (s /= "" && Char.isAlpha (List.head s) && Char.isUpper (List.head s));
		return (Long str s))

mk_pat_app n p =
  if n == Short "ref" then Ast_Pref p
  else 
    case p of 
      Ast_Pcon Nothing ps -> Ast_Pcon (Just n) ps
      _ -> Ast_Pcon (Just n) [p]

-- TODO: negative numbers
-- TODO: underscore patterns
nPbase = 
  fmap Ast_Pvar nV
  <|>
  do n <- nConstructorName;
     return (if n == Short "true" then Ast_Plit (Bool True)
	     else if n == Short "false" then Ast_Plit (Bool False) 
	     else Ast_Pcon (Just n) [])
  <|>
  do i <- tok destIntT;
     return (Ast_Plit (IntLit i))
  <|>
  nPtuple
  <|>
  (tokeq UnderbarT >> return (Ast_Pvar "_"))

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

nLetDec = 
  do tokeq ValT;
     x <- nV;
     tokeq EqualsT;
     e <- nE;
     return (Left (x,e))
  <|>
  (tokeq FunT >> fmap Right nAndFDecls)

nLetDecs = 
  do ld <- nLetDec; lds <- nLetDecs; return (ld : lds)
  <|>
  (tokeq SemicolonT >> nLetDecs)

nDecl =
  do tokeq ValT;
     p <- nPattern;
     tokeq EqualsT;
     e <- nE;
     return (Ast_Dlet p e)
  <|>
  (tokeq FunT >> fmap Ast_Dletrec nAndFDecls)
  <|>
  fmap Ast_Dtype nTypeDec

nDecls = 
  do d <- nDecl;
     ds <- nDecls;
     return (d:ds)
  <|>
  (tokeq SemicolonT >> nDecls)

nSpecLine = 
  do tokeq ValT;
     x <- nV;
     tokeq ColonT;
     t <- nType;
     return (Ast_Sval x t)
  <|>
  (tokeq TypeT >> fmap (\(tn,tvs) -> Ast_Stype_opq tvs tn) nTypeName)
  <|>
  fmap Ast_Stype nTypeDec

nSpecLineList = 
  do s <- nSpecLine;
     ss <- nSpecLineList
     return (s:ss)
  <|>
  (tokeq SemicolonT >> nSpecLineList)

nSignatureValue = 
  do tokeq SigT;
     ss <- nSpecLineList;
     tokeq EndT;
     return ss

nOptionalSignatureAscription = optionMaybe (tokeq SealT >> nSignatureValue)

nStructure = 
  do tokeq StructureT;
     x <- nV;
     s_opt <- nOptionalSignatureAscription;
     tokeq EqualsT;
     tokeq StructT;
     ds <- nDecls;
     tokeq EndT;
     return (Ast_Tmod x s_opt ds)

nTopLevelDec = 
  nStructure
  <|>
  fmap Ast_Tdec nDecl

nREPLTop = 
  do e <- nE; 
     tokeq SemicolonT;
     return (Ast_Tdec (Ast_Dlet (Ast_Pvar "_") e))
  <|>
  do d <- nTopLevelDec;
     tokeq SemicolonT;
     return d
