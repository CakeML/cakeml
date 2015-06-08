module ToSML where
import Ast
import Data.List as List
import Text.PrettyPrint
import Data.Char as Char

infixl <->
(<->) x y = sep [x,y]

-- TODO: might need op sometimes
idToSML :: (Show a) => Id a -> Doc
idToSML (Short x) = 
  if List.elem (show x) ["*", "/", "div", "mod", "+", "-", "^", "::", "@", "<", ">", "<=", ">=", "<>", ":=", "o", "before"] then
    text "op" <+> text (show x)
  else if show x == "=" then
    text "Cake_stub.my_eq"
  else
    text (show x)
idToSML (Long m x) = 
  text (show m) <> text "." <> text (show x)

conIdToSML :: Id ConN -> Doc
conIdToSML (Short x) = 
  if show x == "nil" then
    text "[]"
  else
    idToSML (Short x)
conIdToSML (Long m x) = 
  text (show m) <> text "." <> text (show x)

tcToSML :: Tc -> Doc
tcToSML (TC_name n) = idToSML n
tcToSML TC_int = text "Int.int"
tcToSML TC_char = text "Char.char"
tcToSML TC_string = text "String.string"
tcToSML TC_ref = text "Cake_stub.ref"
tcToSML TC_word8 = text "Word8.word"
tcToSML TC_word8array = text "Word8Array.array"
tcToSML TC_exn = text "Cake_stub.exn"
tcToSML TC_vector = text "Vector.vector"
tcToSML TC_array = text "Array.array"
tcToSML _ = error "internal type representation"

typeToSML :: T -> Doc
typeToSML (Tvar t) = 
  text (show t)
typeToSML (Tapp [t1,t2] TC_fn) =
  parens (typeToSML t1) <+> text "->" <+> parens (typeToSML t2)
typeToSML (Tapp [] TC_tup) =
  text "Cake_stub.unit"
typeToSML (Tapp ts TC_tup) =
  parens (sep (punctuate (text " *") (List.map typeToSML ts)))
typeToSML (Tapp [] tc) =
  tcToSML tc
typeToSML (Tapp [t] tc) =
  typeToSML t <+> tcToSML tc
typeToSML (Tapp ts tc) =
  parens (sep (punctuate comma (List.map typeToSML ts))) <+> tcToSML tc
typeToSML _ =
  error "internal type representation"

escape :: String -> String
escape [] = 
  []
escape (c:s) =
  if c == '\t' then
    '\\' : 't' : escape s
  else if c == '\n' then
    '\\' : 'n' : escape s
  else if c == '"' || c == '\\' then
    '\\' : c : escape s
  else
    c : escape s

litToSML :: Lit -> Doc
litToSML (IntLit i) =
  integer i
litToSML (Char c) =
  if c == '\t' then
    char '#' <> doubleQuotes (text "\\t")
  else if c == '\n' then
    char '#' <> doubleQuotes (text "\\n")
  else if c == '\'' || c == '\\'then
    char '#' <> doubleQuotes (text ['\\',c])
  else
    char '#' <> doubleQuotes (char c)
litToSML (StrLit s) =
  doubleQuotes (text (escape s))
litToSML (Word8 w) =
  error "Word8 not supported" -- TODO

lopToSML :: Lop -> Doc
lopToSML (And _) = text "andalso"
lopToSML (Or _) = text "orelse"

patToSML :: Pat -> Doc
patToSML (Pvar v) = 
  idToSML (Short v)
patToSML (Plit l _) =
  litToSML l
patToSML (Pcon Nothing es _) =
  parens (sep (punctuate comma (List.map patToSML es)))
patToSML (Pcon (Just c) [] _) =
  conIdToSML c
patToSML (Pcon (Just c) es _) =
  conIdToSML c <+> parens (sep (punctuate comma (List.map patToSML es)))
patToSML (Pref p _) =
  parens ((text "ref") <+> patToSML p)

data ExpCtxt = 
    AtomicC
  | AppC

expParen :: ExpCtxt -> Doc -> Doc
expParen AtomicC d = d
expParen AppC d = parens d

expAppToList :: Exp -> [Exp]
expAppToList (App Opapp [e1,e2]) =
  e2 : expAppToList e1
expAppToList e = 
  [e]

-- TODO: option to use bignums or not
opToSML :: Op -> Doc
opToSML (Opn Plus _) = text "Int.+"
opToSML (Opn Minus _) = text "Int.-"
opToSML (Opn Times _) = text "Int.*"
opToSML (Opn Divide _) = text "Int.div"
opToSML (Opn Modulo _) = text "Int.mod"
opToSML (Opb Lt _) = text "Int.<"
opToSML (Opb Gt _) = text "Int.>"
opToSML (Opb Leq _) = text "Int.<="
opToSML (Opb Geq _) = text "Int.>="
opToSML (Equality _) = text "op ="
opToSML (Opassign _) = text "Cake_stub.:="
opToSML (Opref _) = text "ref"
opToSML (Opderef _) = text "Cake_stub.!"
opToSML (Aw8alloc _) = text "Word8Array.array"
opToSML (Aw8sub _) = text "Word8Array.sub"
opToSML (Aw8length _) = text "Word8Array.length"
opToSML (Aw8update _) = text "Word8Array.update"
opToSML (Ord _) = text "Char.ord"
opToSML (Ast.Chr _) = text "Char.chr"
opToSML (Chopb Lt _) = text "Char.<"
opToSML (Chopb Gt _) = text "Char.>"
opToSML (Chopb Leq _) = text "Char.<="
opToSML (Chopb Geq _) = text "Char.>="
opToSML (Implode _) = text "String.implode"
opToSML (Explode _) = text "String.explode"
opToSML (Strlen _) = text "String.size"
opToSML (VfromList _) = text "Vector.fromList"
opToSML (Vsub _) = text "Vector.sub"
opToSML (Vlength _) = text "Vector.length"
opToSML (Aalloc _) = text "Array.array"
opToSML (Asub _) = text "Array.sub"
opToSML (Alength _) = text "Array.length"
opToSML (Aupdate _) = text "Array.update"
opToSML (FFI n _) = error "No ffi for SML"

expToSML :: ExpCtxt -> Exp -> Doc
expToSML c (Raise e) =
  expParen c (text "raise" <+> expToSML AppC e)
expToSML c (Handle e pes) =
  parens ((expToSML AtomicC e <+> text "handle") <-> 
          nest 2 (sep (punctuate (text "|") (List.map patExpToSML pes))))
expToSML c (Lit l _) =
  litToSML l
expToSML c (Con Nothing es _) =
  parens (sep (punctuate comma (List.map (expToSML AtomicC) es)))
expToSML c (Con (Just con) [] _) =
  conIdToSML con
expToSML c (Con (Just con) es _) =
  expParen c (conIdToSML con <+> parens (sep (punctuate comma (List.map (expToSML AtomicC) es))))
expToSML c (Var v) =
  idToSML v
expToSML c (Fun x e _) =
  parens ((text "fn" <+> idToSML (Short x) <+> text "=>") <-> nest 2 (expToSML AtomicC e))
expToSML c (App Opapp es) =
  expParen c (sep (List.map (expToSML AppC) (List.reverse (expAppToList (App Opapp es)))))
expToSML c (App op es) =
  expParen c (opToSML op <+> parens (sep (punctuate comma (List.map (expToSML AtomicC) es))))
expToSML c (Log lop e1 e2) =
  expParen c (((expToSML AppC e1) <+> lopToSML lop) <-> nest 2 (expToSML AppC e2))
expToSML c (If e1 e2 e3) =
  parens ((text "if" <+> expToSML AtomicC e1 <+> text "then") <-> 
           nest 2 (expToSML AtomicC e2) <-> 
	   text "else" <-> nest 2 (expToSML AtomicC e3))
expToSML c (Mat e pes) =
  parens ((text "case" <+> expToSML AtomicC e <+> text "of") <-> 
          nest 2 (sep (punctuate (text "|") (List.map patExpToSML pes))))
expToSML c (Let Nothing e1 e2) =
  parens ((expToSML AtomicC e1 <> semi) <-> expToSML AtomicC e2)
expToSML c (Let (Just v) e1 e2) =
  (text "let val" <+> idToSML (Short v) <+> equals) <-> 
   nest 2 (expToSML AtomicC e1) <-> text "in" <-> nest 2 (expToSML AtomicC e2) <-> text "end"
expToSML c (Letrec funs e) =
  parens (letrecToSML (text "let fun") funs <->
          text "in" <-> 
	  nest 2 (expToSML AtomicC e) <->
          text "end")
 
patExpToSML :: (Pat,Exp) -> Doc
patExpToSML (p,e) =
  (patToSML p <+> text "=>") <-> nest 2 (expToSML AtomicC e)

letrecToSML :: Doc -> [(VarN, VarN, Exp)] -> Doc
letrecToSML head [] = error "empty letrec"
letrecToSML head [(f,x,e)] =
  (head <+> idToSML (Short f) <+> idToSML (Short x) <+> equals) <->
  nest 2 (expToSML AtomicC e)
letrecToSML head ((f,x,e):funs) =
  (head <+> idToSML (Short f) <+> idToSML (Short x) <+> equals) <->
  nest 2 (expToSML AtomicC e) <->
  letrecToSML (text "and") funs

tvsToSML :: [TvarN] -> Doc
tvsToSML [] = empty
tvsToSML [t] = text (show t)
tvsToSML ts = parens (sep (punctuate comma (List.map (text . show) ts)))

conToSML :: (ConN, [T]) -> Doc
conToSML (cn,[]) =
  idToSML (Short cn)
conToSML (cn,ts) =
  idToSML (Short cn) <+> text "of" <+> sep (punctuate (text "*") (List.map typeToSML ts))

dataToSML :: ([TvarN], TypeN, [(ConN, [T])]) -> Doc
dataToSML (tvs, tn, cons) =
  (tvsToSML tvs <+> text (show tn) <+> equals) <->
  nest 2 (sep (punctuate (text "|") (List.map (\c -> conToSML c) cons)))

decToSML :: Dec -> Doc
decToSML (Dlet p e _) =
  text "val" <+> patToSML p <+> equals $+$ 
  nest 2 (expToSML AtomicC e <> semi)
decToSML (Dletrec funs) =
  letrecToSML (text "fun") funs <> semi
decToSML (Dtype td) =
  text "datatype" <+> sep (punctuate (text "and") (List.map dataToSML td)) <> semi
decToSML (Dtabbrev tvs tn t) =
  text "type" <+> tvsToSML tvs <+> text (show tn) <+> equals $+$ 
  nest 2 (typeToSML t <> semi)
decToSML (Dexn cn ts) =
  text "exception" <+> conToSML (cn,ts) <> semi

topToSML :: Top -> Doc
topToSML (Tdec d) =
  decToSML d
topToSML (Tmod mn Nothing ds) =
  text "structure" <+> text (show mn) <+> equals <+> text "struct" $+$ 
  nest 2 (sep (List.map decToSML ds)) $+$
  text "end"
topToSML (Tmod mn (Just sig) ds) =
  error "signatures not supported" -- TODO

progToSML :: Prog -> Doc
progToSML p = vcat (List.map topToSML p)
