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

dummy_pos = initialPos "compiler generated"

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

destTyvarT (TyvarT tv,pos) = Just (TvarN tv pos)
destTyvarT _ = Nothing

tok :: ((Token,SourcePos) -> Maybe a) -> Parsec [(Token,SourcePos)] u a
tok f = token (\t -> show (fst t)) snd f

tokeq t = tok (\(x,pos) -> if t == x then Just pos else Nothing)

linfix exp op = exp `chainl1` fmap (\(t,pos) e1 e2 -> Ast_App (Ast_App (Ast_Var (Short (VarN t pos))) e1) e2) op

longV = 
  tok (\t -> do (str,s,pos) <- destLongidT t;
                guard (s /= "" && (not (isAlpha (List.head s)) || not (isUpper (List.head s))));
                return (Long str (VarN s pos)))

nV' c =
  tok (\t -> do (s,pos) <- destAlphaT t; 
                guard (not (s `elem` ["before", "div", "mod", "o", "true", "false","ref"]) && 
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

mkAst_App e1 e2 =
  case e1 of
    Ast_Con (Just (Short (ConN "ref" pos))) [] pos' -> Ast_App (Ast_Var (Short (VarN "ref" pos))) e2
    Ast_Con s [] pos ->
      case e2 of
        Ast_Con Nothing es pos' -> Ast_Con s es pos
        _ -> Ast_Con s [e2] pos -- Because e2 is an Ebase
    _ -> Ast_App e1 e2

nEapp = do exps <- many1 nEbase;
           return (case exps of
	             [e] -> e
		     (e:es) -> List.foldl mkAst_App e es)

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

eseq_encode pos [] = Ast_Lit Unit pos
eseq_encode pos [e] = e
eseq_encode pos (e:es) = Ast_Let (VarN "_" pos) e (eseq_encode pos es)

nEbaseParen =
  do pos <- tokeq LparT;
     ((tokeq RparT >> return (Ast_Lit Unit pos))
      <|>
      do e1 <- nE;
         choice [tokeq RparT >> return e1,
		 do tokeq CommaT;
                    es <- sepBy1 nE (tokeq CommaT);
		    tokeq RparT;
		    return (Ast_Con Nothing (e1:es) pos),
		 do tokeq SemicolonT;
 		    es <- nEseq;
		    tokeq RparT;
		    return (eseq_encode pos (e1:es))])


do_let_dec (Left (x,e1)) e2 = Ast_Let x e1 e2
do_let_dec (Right funs) e = Ast_Letrec funs e

nEbase = 
  do (i,pos) <- tok destIntT;
     return (Ast_Lit (IntLit i) pos)
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
     return (List.foldr (\e ast -> Ast_Con (Just (Short (ConN "::" pos))) [e, ast] pos) (Ast_Con (Just (Short (ConN "[]" pos))) [] pos) es)
  <|>
  fmap Ast_Var nFQV
  <|>
  do n <- nConstructorName;
     return (case n of
               Short (ConN "true" pos) -> Ast_Lit (Bool True) pos
               Short (ConN "false" pos) -> Ast_Lit (Bool False) pos
	       _ -> Ast_Con (Just n) [] (getPos n))

nEseq = sepBy1 nE (tokeq SemicolonT)

nEmult = linfix nEapp nMultOps

nEadd = linfix nEmult nAddOps

nElist = nEadd `chainr1` fmap (\(t,pos) e1 e2 -> if t == "::" then
                                                   Ast_Con (Just (Short (ConN t pos))) [e1,e2] pos
	                                         else
						   Ast_App (Ast_App (Ast_Var (Short (VarN t pos))) e1) e2)
   
                              nListOps

nErel = linfix nElist nRelOps;

nEcomp = linfix nErel nCompOps

nEbefore = linfix nEcomp (mk_op (AlphaT "before") "before")

nEtyped = 
  do e <- nEbefore;
     option e (tokeq ColonT >> nType >> return e)

nElogicAND = nEtyped `chainl1` (tokeq AndalsoT >>= (\pos -> return (\e1 e2 -> Ast_Log (And pos) e1 e2)))

nElogicOR = nElogicAND `chainl1` (tokeq OrelseT >>= (\pos -> return (\e1 e2 -> Ast_Log (Or pos) e1 e2)))

nEhandle = 
  do e1 <- nElogicOR;
     option e1 (do tokeq HandleT;
                   pes <- nPEs;
		   return (Ast_Handle e1 pes))

nE = 
  (tokeq RaiseT >> fmap Ast_Raise nE)
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
  do pos <- tokeq FnT;
     x <- nV;
     tokeq DarrowT;
     e <- nE;
     return (Ast_Fun x e pos)
  <|>
  do tokeq CaseT;
     e <- nE; 
     tokeq OfT;
     pes <- nPEs;
     return (Ast_Mat e pes)

nE' = 
  (tokeq RaiseT >> fmap Ast_Raise nE)
  <|>
  nEhandle
  <|>
  do tokeq IfT;
     e1 <- nE;
     tokeq ThenT;
     e2 <- nE;
     tokeq ElseT;
     e3 <- nE';
     return (Ast_If e1 e2 e3)

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
multi_funs x (y:ys) e = (x,y,List.foldr (\v e -> Ast_Fun v e (getPos v)) e ys)

nFDecl = do x <- nV;
            ys <- nVlist1;
            tokeq EqualsT;
            e <- nE;
            return (multi_funs x ys e)

nType = nPType `chainr1` (tokeq ArrowT >> return Ast_Tfn)

nDType = do t <- nTbase; 
            ts <- many nTyOp; 
            return (List.foldr (\tc t -> Ast_Tapp [t] (Just tc)) t ts)

nTbase = 
  fmap Ast_Tvar (tok destTyvarT)
  <|>
  fmap (\tc -> (Ast_Tapp [] (Just tc))) nTyOp
  <|>
  do tokeq LparT;
     t <- nType;
     ((tokeq RparT >> return t)
      <|>
      do tokeq CommaT;
         ts <- nTypeList1; 
	 tokeq RparT; 
	 tc <- nTyOp; 
         return (Ast_Tapp (t:ts) (Just tc)))

nTypeList1 = sepBy1 nType (tokeq CommaT)

nTyOp = 
  fmap (Short `o` uncurry TypeN) nUQTyOp
  <|> 
  fmap (\(x,y,pos) -> Long x (TypeN y pos)) (tok destLongidT)

nUQTyOp = tok destAlphaSym

nPType = fmap tuplify (sepBy1 nDType (tokeq StarT))

tuplify [ty] = ty
tuplify tys = Ast_Tapp tys Nothing

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

detuplify (Ast_Tapp args Nothing) = args
detuplify ty = [ty]

nDconstructor = 
  do cn <- nUQConstructorName;
     option (cn,[])
            (do tokeq OfT;
                t <- nType;
                return (cn, detuplify t))

nUQConstructorName = 
  tok (\t -> do (s,pos) <- destAlphaT t; 
                guard (s /= "" && isUpper (List.head s) || s `elem` ["true", "false", "ref"]);
                return (ConN s pos))

nConstructorName = 
  fmap Short nUQConstructorName
  <|>
  tok (\t -> do (str,s,pos) <- destLongidT t;
                guard (s /= "" && Char.isAlpha (List.head s) && Char.isUpper (List.head s));
	        return (Long str (ConN s pos)))

mk_pat_app n p =
  case n of
    Short (ConN "ref" pos) -> Ast_Pref p pos
    _ -> case p of 
           Ast_Pcon Nothing ps pos' -> Ast_Pcon (Just n) ps (getPos n)
           _ -> Ast_Pcon (Just n) [p] (getPos n)

-- TODO: negative numbers
-- TODO: underscore patterns
nPbase = 
  fmap Ast_Pvar nV
  <|>
  do n <- nConstructorName;
     return (case n of 
	       Short (ConN "true" pos) -> Ast_Plit (Bool True) pos
	       Short (ConN "false" pos) -> Ast_Plit (Bool False) pos
	       _ -> Ast_Pcon (Just n) [] (getPos n))
  <|>
  do (i,pos) <- tok destIntT;
     return (Ast_Plit (IntLit i) pos)
  <|>
  nPtuple
  <|>
  (tokeq UnderbarT >>= (\pos -> return (Ast_Pvar (VarN "_" pos))))
  <|>
  do pos <- tokeq LbrackT;
     ps <- sepBy nPattern (tokeq CommaT);
     tokeq RbrackT;
     return (List.foldr (\p ast -> Ast_Pcon (Just (Short (ConN "::" pos))) [p, ast] pos) (Ast_Pcon (Just (Short (ConN "[]" pos))) [] pos) ps)


nPapp = choice [try (do n <- nConstructorName;
                        pat <- nPbase;
                        return (mk_pat_app n pat)), 
                nPbase]

nPattern = nPapp `chainr1` fmap (\pos p1 p2 -> Ast_Pcon (Just (Short (ConN "::" pos))) [p1,p2] pos) (tokeq (SymbolT "::"))  

nPtuple = 
  do pos <- tokeq LparT;
     ((tokeq RparT >> return (Ast_Plit Unit pos))
      <|> 
      do pats <- sepBy1 nPattern (tokeq CommaT);
         tokeq RparT;
         return (Ast_Pcon Nothing pats pos))

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
  <|> many (fail "")

nDecl =
  do pos <- tokeq ValT;
     p <- nPattern;
     tokeq EqualsT;
     e <- nE;
     return (Ast_Dlet p e pos)
  <|>
  (tokeq FunT >> fmap Ast_Dletrec nAndFDecls)
  <|>
  fmap Ast_Dtype nTypeDec
  <|>
  (tokeq ExceptionT >> fmap (uncurry Ast_Dexn) nDconstructor)

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
  <|>
  many (fail "")

nSignatureValue = between (tokeq SigT) (tokeq EndT) nSpecLineList 

nOptionalSignatureAscription = optionMaybe (tokeq SealT >> nSignatureValue)

nStructure = 
  do tokeq StructureT;
     x <- nV' ModN;
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

nREPLTop :: ParsecT [(Token,SourcePos)] u DFI.Identity Ast_top
nREPLTop = 
  do e <- nE; 
     pos <- tokeq SemicolonT;
     return (Ast_Tdec (Ast_Dlet (Ast_Pvar (VarN "_" pos)) e pos))
  <|>
  do d <- nTopLevelDec;
     tokeq SemicolonT;
     return d

parseTop :: [(Token,SourcePos)] -> Either ParseError Ast_top
parseTop toks = parse nREPLTop "" toks
