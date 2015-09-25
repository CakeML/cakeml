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
import Data.Functor.Identity as DFI

o f g x = f (g x)

destLongidT (LongidT x y,pos) = Just (ModN x pos,y,pos)
destLongidT _ = Nothing

destAlphaT (AlphaT x,pos) = Just (x,pos)
destAlphaT _ = Nothing

destSymbolT (SymbolT x,pos) = Just (x,pos)
destSymbolT _ = Nothing

destAlphaSym (AlphaT x,pos) = Just (x,pos)
destAlphaSym (SymbolT x,pos) = Just (x,pos)
destAlphaSym _ = Nothing

destIntT (IntT i,pos) = Just (i,pos)
destIntT _ = Nothing

destStringT (StringT s,pos) = Just (s,pos)
destStringT _ = Nothing

destTyvarT (TyvarT tv,pos) = Just (TvarN tv pos)
destTyvarT _ = Nothing

tok :: ((Token,SourcePos) -> Maybe a) -> Parsec [(Token,SourcePos)] u a
tok f = token (\t -> show (fst t)) snd f

tokeq t = tok (\(x,pos) -> if t == x then Just pos else Nothing)

linfix exp op = exp `chainl1` fmap (\(t,pos) e1 e2 -> App Opapp [App Opapp [Var (Short (VarN t pos)), e1], e2]) op

longV = 
  tok (\t -> do (str,s,pos) <- destLongidT t;
                guard (s /= "" && (not (isAlpha (List.head s)) || not (isUpper (List.head s))));
                return (Long str (VarN s pos)))

nV' c =
  tok (\t -> do (s,pos) <- destAlphaT t; 
                guard (not (s `elem` ["before", "div", "mod", "o", "true", "false","ref", "nil"]) && 
                       s /= "" && 
	               not (isUpper (List.head s)));
	        return (c s pos))
  <|>
  tok (\t -> do (s,pos) <- destSymbolT t;
                guard (not (s `elem` ["+", "-", "/", "<", ">", "<=", ">=", "<>", ":=", "*", "::", "@"]));
	        return (c s pos))

nV = nV' VarN

nVlist1 = many1 nV

nFQV = fmap Short nV <|> longV

mkApp e1 e2 =
  case e1 of
    Con (Just (Short (ConN "ref" pos))) [] pos' -> App Opapp [Var (Short (VarN "ref" pos)), e2]
    Con s [] pos ->
      case e2 of
        Con Nothing es pos' -> Con s es pos
        _ -> Con s [e2] pos -- Because e2 is an Ebase
    _ -> App Opapp [e1,e2]

nEapp = do exps <- many1 nEbase;
           return (case exps of
	             [e] -> e
		     (e:es) -> List.foldl mkApp e es)

mk_op tok str =
  tokeq tok >>= (\pos -> return (str,pos))

nMultOps = 
  (mk_op StarT "*")
  <|>
  (mk_op (SymbolT "/") "/")
  <|> 
  (mk_op (AlphaT "mod") "mod")
  <|>
  (mk_op (AlphaT "div") "div")

nAddOps = 
  (mk_op (SymbolT "+") "+")
  <|>
  (mk_op (SymbolT "-") "-")

nRelOps = choice (mk_op EqualsT "=" : List.map (\s -> mk_op (SymbolT s) s) ["<", ">", "<=", ">=", "<>"])

nListOps = choice (List.map (\s -> mk_op (SymbolT s) s) ["::", "@"])

nCompOps = 
  (mk_op (SymbolT ":=") ":=")
  <|>
  (mk_op (AlphaT "o") "o")

eseq_encode pos [] = Con Nothing [] pos
eseq_encode pos [e] = e
eseq_encode pos (e:es) = Let Nothing e (eseq_encode pos es)

nEbaseParen =
  do pos <- tokeq LparT;
     ((tokeq RparT >> return (Con Nothing [] pos))
      <|>
      do e1 <- nE;
         choice [tokeq RparT >> return e1,
		 do tokeq CommaT;
                    es <- sepBy1 nE (tokeq CommaT);
		    tokeq RparT;
		    return (Con Nothing (e1:es) pos),
		 do tokeq SemicolonT;
 		    es <- nEseq;
		    tokeq RparT;
		    return (eseq_encode pos (e1:es))])


do_let_dec (Left (x,e1)) e2 = Let x e1 e2
do_let_dec (Right funs) e = Letrec funs e

nEbase = 
  do (i,pos) <- tok destIntT;
     return (Lit (IntLit i) pos)
  <|>
  do (s,pos) <- tok destStringT;
     return (Lit (StrLit s) pos)
  <|>
  nEbaseParen
  <|>
  do tokeq LetT;
     lets <- nLetDecs;
     pos <- tokeq InT;
     es <- nEseq;
     tokeq EndT;
     return (List.foldr do_let_dec (eseq_encode pos es) lets)
  <|>
  do pos <- tokeq LbrackT;
     es <- sepBy nE (tokeq CommaT);
     tokeq RbrackT;
     return (List.foldr (\e ast -> Con (Just (Short (ConN "::" pos))) [e, ast] pos) (Con (Just (Short (ConN "nil" pos))) [] pos) es)
  <|>
  fmap Var nFQV
  <|>
  do n <- nConstructorName;
     return (Con (Just n) [] (getPos n))

nEseq = sepBy1 nE (tokeq SemicolonT)

nEmult = linfix nEapp nMultOps

nEadd = linfix nEmult nAddOps

nElist = nEadd `chainr1` fmap (\(t,pos) e1 e2 -> if t == "::" then
                                                   Con (Just (Short (ConN t pos))) [e1,e2] pos
	                                         else
						   App Opapp [App Opapp [Var (Short (VarN t pos)), e1], e2])
   
                              nListOps

nErel = linfix nElist nRelOps;

nEcomp = linfix nErel nCompOps

nEbefore = linfix nEcomp (mk_op (AlphaT "before") "before")

nEtyped = 
  do e <- nEbefore;
     option e (tokeq ColonT >> nType >> return e)

nElogicAND = nEtyped `chainl1` (tokeq AndalsoT >>= (\pos -> return (\e1 e2 -> Log (And pos) e1 e2)))

nElogicOR = nElogicAND `chainl1` (tokeq OrelseT >>= (\pos -> return (\e1 e2 -> Log (Or pos) e1 e2)))

nEhandle = 
  do e1 <- nElogicOR;
     option e1 (do tokeq HandleT;
                   pes <- nPEs;
		   return (Handle e1 pes))

nE = 
  (tokeq RaiseT >> fmap Raise nE)
  <|>
  nEhandle
  <|>
  do tokeq IfT;
     e1 <- nE;
     tokeq ThenT;
     e2 <- nE;
     tokeq ElseT;
     e3 <- nE;
     return (If e1 e2 e3)
  <|>
  do pos <- tokeq FnT;
     x <- nV;
     tokeq DarrowT;
     e <- nE;
     return (Fun x e pos)
  <|>
  do tokeq CaseT;
     e <- nE; 
     tokeq OfT;
     pes <- nPEs;
     return (Mat e pes)

nE' = 
  (tokeq RaiseT >> fmap Raise nE)
  <|>
  nEhandle
  <|>
  do tokeq IfT;
     e1 <- nE;
     tokeq ThenT;
     e2 <- nE;
     tokeq ElseT;
     e3 <- nE';
     return (If e1 e2 e3)

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
multi_funs x (y:ys) e = (x,y,List.foldr (\v e -> Fun v e (getPos v)) e ys)

nFDecl = do x <- nV;
            ys <- nVlist1;
            tokeq EqualsT;
            e <- nE;
            return (multi_funs x ys e)

nType = nPType `chainr1` (tokeq ArrowT >> return (\t1 t2 -> Tapp [t1,t2] TC_fn))

nDType = do t <- nTbase; 
            ts <- many nTyOp; 
            return (List.foldr (\tc t -> Tapp [t] (TC_name tc)) t ts)

nTbase = 
  fmap Tvar (tok destTyvarT)
  <|>
  fmap (\tc -> (Tapp [] (TC_name tc))) nTyOp
  <|>
  do tokeq LparT;
     t <- nType;
     ((tokeq RparT >> return t)
      <|>
      do tokeq CommaT;
         ts <- nTypeList1; 
	 tokeq RparT; 
	 tc <- nTyOp; 
         return (Tapp (t:ts) (TC_name tc)))

nTypeList1 = sepBy1 nType (tokeq CommaT)

nTyOp = 
  fmap (Short `o` uncurry TypeN) nUQTyOp
  <|> 
  fmap (\(x,y,pos) -> Long x (TypeN y pos)) (tok destLongidT)

nUQTyOp = tok destAlphaSym

nPType = fmap tuplify (sepBy1 nDType (tokeq StarT))

tuplify [ty] = ty
tuplify tys = Tapp tys TC_tup

nTypeName = 
  fmap (\n -> (uncurry TypeN n,[])) nUQTyOp
  <|>
  do tokeq LparT;
     tvs <- nTyVarList;
     tokeq RparT;
     n <- nUQTyOp;
     return (uncurry TypeN n, tvs)
  <|>
  do tv <- tok destTyvarT;
     n <- nUQTyOp;
     return (uncurry TypeN n, [tv])

nTyVarList = sepBy1 (tok destTyvarT) (tokeq CommaT)

nTypeDec = 
  tokeq DatatypeT >> sepBy1 nDtypeDecl (tokeq AndT)

nDtypeDecl = 
  do (tn,tvs) <- nTypeName; 
     tokeq EqualsT;
     ctors <- sepBy1 nDconstructor (tokeq BarT);
     return (tvs,tn,ctors)

detuplify (Tapp args TC_tup) = args
detuplify ty = [ty]

nDconstructor = 
  do cn <- nUQConstructorName;
     option (cn,[])
            (do tokeq OfT;
                t <- nType;
                return (cn, detuplify t))

nStructName = 
  tok (\t -> do (s,pos) <- destAlphaT t; 
                guard (s /= "");
                return (ModN s pos))

nUQConstructorName = 
  tok (\t -> do (s,pos) <- destAlphaT t; 
                guard (s /= "" && isUpper (List.head s) || s `elem` ["true", "false", "ref", "nil"]);
                return (ConN s pos))

nConstructorName = 
  fmap Short nUQConstructorName
  <|>
  tok (\t -> do (str,s,pos) <- destLongidT t;
                guard (s /= "" && Char.isAlpha (List.head s) && Char.isUpper (List.head s));
	        return (Long str (ConN s pos)))

mk_pat_app n p =
  case n of
    Short (ConN "ref" pos) -> Pref p pos
    _ -> case p of 
           Pcon Nothing ps pos' -> Pcon (Just n) ps (getPos n)
           _ -> Pcon (Just n) [p] (getPos n)

-- TODO: negative numbers
-- TODO: underscore patterns
nPbase = 
  fmap Pvar nV
  <|>
  do n <- nConstructorName;
     return (Pcon (Just n) [] (getPos n))
  <|>
  do (i,pos) <- tok destIntT;
     return (Plit (IntLit i) pos)
  <|>
  do (s,pos) <- tok destStringT;
     return (Plit (StrLit s) pos)
  <|>
  nPtuple
  <|>
  (tokeq UnderbarT >>= (\pos -> return (Pvar (VarN "_" pos))))
  <|>
  do pos <- tokeq LbrackT;
     ps <- sepBy nPattern (tokeq CommaT);
     tokeq RbrackT;
     return (List.foldr (\p ast -> Pcon (Just (Short (ConN "::" pos))) [p, ast] pos) (Pcon (Just (Short (ConN "nil" pos))) [] pos) ps)


nPapp = choice [try (do n <- nConstructorName;
                        pat <- nPbase;
                        return (mk_pat_app n pat)), 
                nPbase]

nPattern = nPapp `chainr1` fmap (\pos p1 p2 -> Pcon (Just (Short (ConN "::" pos))) [p1,p2] pos) (tokeq (SymbolT "::"))  
nPtuple = 
  do pos <- tokeq LparT;
     ((tokeq RparT >> return (Pcon Nothing [] pos))
      <|> 
      do pat <- nPattern;
         r <- option pat (do tokeq CommaT 
                             pats <- sepBy1 nPattern (tokeq CommaT)
                             return (Pcon Nothing (pat:pats) pos));
         tokeq RparT;
         return r)

nLetDec = 
  do tokeq ValT;
     x <- nV;
     tokeq EqualsT;
     e <- nE;
     return (Left (Just x,e))
  <|>
  (tokeq FunT >> fmap Right nAndFDecls)

nLetDecs = 
  do ld <- nLetDec; lds <- nLetDecs; return (ld : lds)
  <|>
  (tokeq SemicolonT >> nLetDecs)
  <|> many (fail "")

nDecl =
  do pos <- tokeq ValT;
     p <- nPattern;
     tokeq EqualsT;
     e <- nE;
     return (Dlet p e pos)
  <|>
  (tokeq FunT >> fmap Dletrec nAndFDecls)
  <|>
  fmap Dtype nTypeDec
  <|>
  (tokeq ExceptionT >> fmap (uncurry Dexn) nDconstructor)
  <|> 
  do tokeq TypeT;
     (tn,tvs) <- nTypeName; 
     tokeq EqualsT;
     t <- nType;
     return (Dtabbrev tvs tn t)

nDecls = 
  do d <- nDecl;
     ds <- nDecls;
     return (d:ds)
  <|>
  (tokeq SemicolonT >> nDecls)
  <|>
  many (fail "")

nSpecLine = 
  do tokeq ValT;
     x <- nV;
     tokeq ColonT;
     t <- nType;
     return (Sval x t)
  <|>
  (tokeq TypeT >> fmap (\(tn,tvs) -> Stype_opq tvs tn) nTypeName)
  <|>
  fmap Stype nTypeDec

nSpecLineList = 
  do s <- nSpecLine;
     ss <- nSpecLineList
     return (s:ss)
  <|>
  (tokeq SemicolonT >> nSpecLineList)
  <|>
  many (fail "")

nSignatureValue = between (tokeq SigT) (tokeq EndT) nSpecLineList 

nOptionalSignatureAscription = optionMaybe (tokeq SealT >> nSignatureValue)

nStructure = 
  do tokeq StructureT;
     x <- nStructName;
     s_opt <- nOptionalSignatureAscription;
     tokeq EqualsT;
     tokeq StructT;
     ds <- nDecls;
     tokeq EndT;
     return (Tmod x s_opt ds)

nTopLevelDec = 
  nStructure
  <|>
  fmap Tdec nDecl

nREPLTop :: ParsecT [(Token,SourcePos)] u DFI.Identity Top
nREPLTop = 
  do e <- nE; 
     pos <- tokeq SemicolonT;
     return (Tdec (Dlet (Pvar (VarN "it" pos)) e pos))
  <|>
  do d <- nTopLevelDec;
     tokeq SemicolonT;
     return d

parseTop :: [(Token,SourcePos)] -> Either ParseError Top
parseTop toks = parse nREPLTop "" toks
