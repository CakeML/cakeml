module ToOCaml where
import Ast
import Data.List as List
import Text.PrettyPrint

typeToOCaml :: T -> Doc
typeToOCaml (Tvar t) = 
  text (show t)
typeToOCaml (Tapp [t1,t2] TC_fn) =
  parens (typeToOCaml t1) <+> text "->" <+> parens (typeToOCaml t2)
typeToOCaml (Tapp ts TC_tup) =
  parens (sep (punctuate (text "*") (List.map typeToOCaml ts)))
typeToOCaml (Tapp [] tc) =
  text (show tc)
typeToOCaml (Tapp ts tc) =
  parens (sep (punctuate comma (List.map typeToOCaml ts))) <+> text (show tc)
typeToOCaml _ =
  error "internal type representation"

litToOCaml :: Lit -> Doc
litToOCaml (IntLit i) =
  integer i
litToOCaml (Char c) =
  quotes (char c)
litToOCaml (StrLit s) =
  doubleQuotes (text s)
litToOCaml (Word8 w) =
  error "Word8 not supported"

idToOCaml :: (Show a) => Id a -> Doc
idToOCaml (Short x) = 
  text (show x)
idToOCaml (Long m x) = 
  text (show m) <> text "." <> text (show x)

lopToOCaml :: Lop -> Doc
lopToOCaml (And _) = text "&&"
lopToOCaml (Or _) = text "||"

patToOCaml :: Pat -> Doc
patToOCaml (Pvar v) = 
  text (show v)
patToOCaml (Plit l _) =
  litToOCaml l
patToOCaml (Pcon Nothing es _) =
  parens (sep (punctuate comma (List.map patToOCaml es)))
patToOCaml (Pcon (Just c) es _) =
  idToOCaml c <+> parens (sep (punctuate comma (List.map patToOCaml es)))
patToOCaml (Pref p _) =
  braces (text "Pervasives.contents =" <+> patToOCaml p)

expToOCaml :: Exp -> Doc
expToOCaml (Raise e) =
  text "raise" <+> parens (expToOCaml e)
expToOCaml (Handle e pes) =
  text "try" <+> expToOCaml e <+> text "with" <+> sep (List.map patExpToOCaml pes)
expToOCaml (Lit l _) =
  litToOCaml l
expToOCaml (Con Nothing es _) =
  parens (sep (punctuate comma (List.map expToOCaml es)))
expToOCaml (Con (Just c) es _) =
  idToOCaml c <+> parens (sep (punctuate comma (List.map expToOCaml es)))
expToOCaml (Var v) =
  idToOCaml v
expToOCaml (Fun x e _) =
  text "fun" <+> text (show x) <+> text "->" <+> expToOCaml e
expToOCaml (App Opapp es) =
  sep (List.map parens (List.map expToOCaml es))
expToOCaml (App _ es) =
  error "Internal error"
expToOCaml (Log lop e1 e2) =
  parens (expToOCaml e1) <+> lopToOCaml lop <+> parens (expToOCaml e2)
expToOCaml (If e1 e2 e3) =
  text "if" <+> expToOCaml e1 <+> text "then" <+> expToOCaml e2 <+> text "else" <+> expToOCaml e3
expToOCaml (Mat e pes) =
  text "match" <+> expToOCaml e <+> text "with" <+> sep (List.map patExpToOCaml pes)
expToOCaml (Let Nothing e1 e2) =
  parens (expToOCaml e1 <> semi <+> expToOCaml e2)
expToOCaml (Let (Just v) e1 e2) =
  text "let" <+> text (show v) <+> equals <+> expToOCaml e1 <+> text "in" <+> expToOCaml e2
expToOCaml (Letrec funs e) =
  text "let rec" <+> 
  sep (punctuate (text "and") (List.map (\(f,x,e) -> text (show f) <+> text (show x) <+> equals <+> expToOCaml e) funs)) <+> 
  text "in" <+> 
  expToOCaml e
 
patExpToOCaml :: (Pat,Exp) -> Doc
patExpToOCaml (p,e) =
  text "|" <+> patToOCaml p <+> text "->" <+> parens (expToOCaml e)

tvsToOCaml :: [TvarN] -> Doc
tvsToOCaml [] = empty
tvsToOCaml ts = parens (sep (List.map (text . show) ts))

conToOCaml :: (ConN, [T]) -> Doc
conToOCaml (cn,ts) =
  text (show cn) <+> text "of" <+> sep (punctuate (text "*") (List.map typeToOCaml ts))

dataToOCaml :: ([TvarN], TypeN, [(ConN, [T])]) -> Doc
dataToOCaml (tvs, tn, cons) =
  tvsToOCaml tvs <+> text (show tn) <+> equals <+> sep (List.map (\c -> text "|" <+> conToOCaml c) cons)

decToOCaml :: Dec -> Doc
decToOCaml (Dlet p e _) =
  text "let" <+> patToOCaml p <+> equals <+> expToOCaml e <> semi <> semi
decToOCaml (Dletrec funs) =
  text "let rec" <+> 
  sep (punctuate (text "and") (List.map (\(f,x,e) -> text (show f) <+> text (show x) <+> equals <+> expToOCaml e) funs)) <> 
  semi <> semi
decToOCaml (Dtype td) =
  text "type" <+> sep (punctuate (text "and") (List.map dataToOCaml td)) <> semi <> semi
decToOCaml (Dtabbrev tvs tn t) =
  text "type" <+> tvsToOCaml tvs <+> text (show tn) <+> equals <+> typeToOCaml t <> semi <> semi
decToOCaml (Dexn cn ts) =
  text "exception" <+> conToOCaml (cn,ts) <> semi <> semi

topToOCaml :: Top -> Doc
topToOCaml (Tdec d) =
  decToOCaml d
topToOCaml (Tmod mn Nothing ds) =
  text "module" <+> text (show mn) <+> equals <+> text "struct" <+> 
  sep (List.map decToOCaml ds) <+>
  text "end"
topToOCaml (Tmod mn (Just sig) ds) =
  error "signatures not supported"

progToOCaml :: Prog -> Doc
progToOCaml p = vcat (List.map topToOCaml p)
