module ToOCaml where
import Ast
import Data.List as List
import Text.PrettyPrint
import Data.Char as Char

infixl <->
(<->) x y = sep [x,y]

idParens :: String -> Doc
idParens s =
  if List.head s == '*' then
    text ("( " ++ s ++ " )")
  else if Char.isAlphaNum (List.head s) && not (s == "mod") then
    text s
  else
    parens (text s)

-- TODO detect idents that won't work, try to infix some
idToOCaml :: (Show a) => Id a -> Doc
idToOCaml (Short x) = 
  idParens (show x)
idToOCaml (Long m x) = 
  text (show m) <> text "." <> idParens (show x)

conIdToOCaml :: Id ConN -> Doc
conIdToOCaml (Short x) = 
  if show x == "nil" then
    text "[]"
  else
    idToOCaml (Short x)
conIdToOCaml (Long m x) = 
  text (show m) <> text "." <> idParens (show x)

tcToOCaml :: Tc -> Doc
tcToOCaml (TC_name n) = idToOCaml n
tcToOCaml TC_int = text "Cake_stub.int"
tcToOCaml TC_char = text "Cake_stub.char"
tcToOCaml TC_string = text "Cake_stub.string"
tcToOCaml TC_ref = text "Pervasives.ref"
tcToOCaml TC_word8 = text "Cake_stub.char"
tcToOCaml TC_word8array = text "Cake_stub.bytes"
tcToOCaml TC_exn = text "Cake_stub.exn"
tcToOCaml TC_vector = text "Cake_stub.array"
tcToOCaml TC_array = text "Cake_stub.array"
tcToOCaml _ = error "internal type representation"

typeToOCaml :: T -> Doc
typeToOCaml (Tvar t) = 
  text (show t)
typeToOCaml (Tapp [t1,t2] TC_fn) =
  parens (typeToOCaml t1) <+> text "->" <+> parens (typeToOCaml t2)
typeToOCaml (Tapp ts TC_tup) =
  parens (sep (punctuate (text " *") (List.map typeToOCaml ts)))
typeToOCaml (Tapp [] tc) =
  tcToOCaml tc
typeToOCaml (Tapp [t] tc) =
  typeToOCaml t <+> tcToOCaml tc
typeToOCaml (Tapp ts tc) =
  parens (sep (punctuate comma (List.map typeToOCaml ts))) <+> tcToOCaml tc
typeToOCaml _ =
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

litToOCaml :: Lit -> Doc
litToOCaml (IntLit i) =
  integer i
litToOCaml (Char c) =
  if c == '\t' then
    quotes (text "\\t")
  else if c == '\n' then
    quotes (text "\\n")
  else if c == '\'' || c == '\\'then
    quotes (text ['\\',c])
  else
    quotes (char c)
litToOCaml (StrLit s) =
  doubleQuotes (text (escape s))
litToOCaml (Word8 w) =
  error "Word8 not supported" -- TODO

lopToOCaml :: Lop -> Doc
lopToOCaml (And _) = text "&&"
lopToOCaml (Or _) = text "||"

patToOCaml :: Pat -> Doc
patToOCaml (Pvar v) = 
  idParens (show v)
patToOCaml (Plit l _) =
  litToOCaml l
patToOCaml (Pcon Nothing es _) =
  parens (sep (punctuate comma (List.map patToOCaml es)))
patToOCaml (Pcon (Just c) [] _) =
  conIdToOCaml c
patToOCaml (Pcon (Just c) es _) =
  conIdToOCaml c <+> parens (sep (punctuate comma (List.map patToOCaml es)))
patToOCaml (Pref p _) =
  braces (text "Pervasives.contents =" <+> patToOCaml p)

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
-- TODO: The OCaml mod semantics are different from SML. Unsure about the div semantics.
-- TODO: Also, check the various exceptions.
opToOCaml :: Op -> Doc
opToOCaml (Opn Plus _) = text "Pervasives.(+)"
opToOCaml (Opn Minus _) = text "Pervasives.(-)"
opToOCaml (Opn Times _) = text "Pervasives.( * )"
opToOCaml (Opn Divide _) = text "Pervasives.(/)"
opToOCaml (Opn Modulo _) = text "Pervasives.(mod)"
opToOCaml (Opb Lt _) = text "Pervasives.(<)"
opToOCaml (Opb Gt _) = text "Pervasives.(>)"
opToOCaml (Opb Leq _) = text "Pervasives.(<=)"
opToOCaml (Opb Geq _) = text "Pervasives.(>=)"
opToOCaml (Equality _) = text "Pervasives.(=)"
opToOCaml (Opassign _) = text "Pervasives.(:=)"
opToOCaml (Opref _) = text "Pervasives.ref"
opToOCaml (Opderef _) = text "Pervasives.(!)"
opToOCaml (Aw8alloc _) = text "Bytes.make"
opToOCaml (Aw8sub _) = text "Bytes.get"
opToOCaml (Aw8length _) = text "Bytes.length"
opToOCaml (Aw8update _) = text "Bytes.set"
opToOCaml (Ord _) = text "Char.code"
opToOCaml (Ast.Chr _) = text "Char.chr"
opToOCaml (Chopb Lt _) = text "Pervasives.(<)"
opToOCaml (Chopb Gt _) = text "Pervasives.(>)"
opToOCaml (Chopb Leq _) = text "Pervasives.(<=)"
opToOCaml (Chopb Geq _) = text "Pervasives.(>=)"
opToOCaml (Implode _) = text "Cake_stub.implode"
opToOCaml (Explode _) = text "Cake_stub.explode"
opToOCaml (Strlen _) = text "String.length"
-- OCaml doesn't have vectors, so translate to arrays
opToOCaml (VfromList _) = text "Array.of_list"
opToOCaml (Vsub _) = text "Array.get"
opToOCaml (Vlength _) = text "Array.length"
opToOCaml (Aalloc _) = text "Array.make"
opToOCaml (Asub _) = text "Array.get"
opToOCaml (Alength _) = text "Array.length"
opToOCaml (Aupdate _) = text "Array.set"
opToOCaml (FFI n _) = error "No ffi for OCaml"

expToOCaml :: ExpCtxt -> Exp -> Doc
expToOCaml c (Raise e) =
  expParen c (text "raise" <+> expToOCaml AppC e)
expToOCaml c (Handle e pes) =
  parens ((text "try" <+> expToOCaml AtomicC e <+> text "with") <-> 
          nest 2 (sep (List.map patExpToOCaml pes)))
expToOCaml c (Lit l _) =
  litToOCaml l
expToOCaml c (Con Nothing es _) =
  parens (sep (punctuate comma (List.map (expToOCaml AtomicC) es)))
expToOCaml c (Con (Just con) [] _) =
  conIdToOCaml con
expToOCaml c (Con (Just con) es _) =
  expParen c (conIdToOCaml con <+> parens (sep (punctuate comma (List.map (expToOCaml AtomicC) es))))
expToOCaml c (Var v) =
  idToOCaml v
expToOCaml c (Fun x e _) =
  parens ((text "fun" <+> idParens (show x) <+> text "->") <-> nest 2 (expToOCaml AtomicC e))
expToOCaml c (App Opapp es) =
  expParen c (sep (List.map (expToOCaml AppC) (List.reverse (expAppToList (App Opapp es)))))
expToOCaml c (App op es) =
  expParen c (sep (opToOCaml op : List.map (expToOCaml AppC) es))
expToOCaml c (Log lop e1 e2) =
  expParen c (((expToOCaml AppC e1) <+> lopToOCaml lop) <-> nest 2 (expToOCaml AppC e2))
expToOCaml c (If e1 e2 e3) =
  parens ((text "if" <+> expToOCaml AtomicC e1 <+> text "then") <-> 
           nest 2 (expToOCaml AtomicC e2) <-> 
	   text "else" <-> nest 2 (expToOCaml AtomicC e3))
expToOCaml c (Mat e pes) =
  parens ((text "match" <+> expToOCaml AtomicC e <+> text "with") <-> 
          nest 2 (sep (List.map patExpToOCaml pes)))
expToOCaml c (Let Nothing e1 e2) =
  parens ((expToOCaml AtomicC e1 <> semi) <-> expToOCaml AtomicC e2)
expToOCaml c (Let (Just v) e1 e2) =
  parens ((text "let" <+> idParens (show v) <+> equals) <-> 
           nest 2 (expToOCaml AtomicC e1) <-> text "in" <-> nest 2 (expToOCaml AtomicC e2))
expToOCaml c (Letrec funs e) =
  parens (letrecToOCaml (text "let rec") funs <->
          text "in" <-> 
	  nest 2 (expToOCaml AtomicC e))
 
patExpToOCaml :: (Pat,Exp) -> Doc
patExpToOCaml (p,e) =
  (text "|" <+> patToOCaml p <+> text "->") <-> nest 2 (expToOCaml AtomicC e)

letrecToOCaml :: Doc -> [(VarN, VarN, Exp)] -> Doc
letrecToOCaml head [] = error "empty letrec"
letrecToOCaml head [(f,x,e)] =
  (head <+> idParens (show f) <+> idParens (show x) <+> equals) <->
  nest 2 (expToOCaml AtomicC e)
letrecToOCaml head ((f,x,e):funs) =
  (head <+> idParens (show f) <+> idParens (show x) <+> equals) <->
  nest 2 (expToOCaml AtomicC e) <->
  letrecToOCaml (text "and") funs

tvsToOCaml :: [TvarN] -> Doc
tvsToOCaml [] = empty
tvsToOCaml [t] = text (show t)
tvsToOCaml ts = parens (sep (punctuate comma (List.map (text . show) ts)))

conToOCaml :: (ConN, [T]) -> Doc
conToOCaml (cn,[]) =
  idParens (show cn)
conToOCaml (cn,ts) =
  idParens (show cn) <+> text "of" <+> sep (punctuate (text "*") (List.map typeToOCaml ts))

dataToOCaml :: ([TvarN], TypeN, [(ConN, [T])]) -> Doc
dataToOCaml (tvs, tn, cons) =
  (tvsToOCaml tvs <+> text (show tn) <+> equals) <->
  nest 2 (sep (List.map (\c -> text "|" <+> conToOCaml c) cons))

decToOCaml :: Dec -> Doc
decToOCaml (Dlet p e _) =
  text "let" <+> patToOCaml p <+> equals $+$ 
  nest 2 (expToOCaml AtomicC e <> semi <> semi)
decToOCaml (Dletrec funs) =
  letrecToOCaml (text "let rec") funs <> semi <> semi
decToOCaml (Dtype td) =
  text "type" <+> sep (punctuate (text "and") (List.map dataToOCaml td)) <> semi <> semi
decToOCaml (Dtabbrev tvs tn t) =
  text "type" <+> tvsToOCaml tvs <+> text (show tn) <+> equals $+$ 
  nest 2 (typeToOCaml t <> semi <> semi)
decToOCaml (Dexn cn ts) =
  text "exception" <+> conToOCaml (cn,ts) <> semi <> semi

topToOCaml :: Top -> Doc
topToOCaml (Tdec d) =
  decToOCaml d
topToOCaml (Tmod mn Nothing ds) =
  text "module" <+> text (show mn) <+> equals <+> text "struct" $+$ 
  nest 2 (sep (List.map decToOCaml ds)) $+$
  text "end"
topToOCaml (Tmod mn (Just sig) ds) =
  error "signatures not supported" -- TODO

progToOCaml :: Prog -> Doc
progToOCaml p = vcat (List.map topToOCaml p)
