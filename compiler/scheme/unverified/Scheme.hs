module Scheme where
import Data.Typeable (cast)
import Data.Char (ord, isSpace, toLower)
import Data.Maybe (fromMaybe)
import Control.Monad (liftM2, guard)
import Control.Applicative ((<|>))
import Data.Either.Extra (maybeToEither)
import Data.Tuple (swap)

data ArithOp = Plus | Minus | Multiply
    deriving (Show, Eq)
data Token = Open | Close | Value SValue | Identifier String
    deriving Show

data Datum = ExpList [Datum] | Const SValue | Symbol String
    deriving Show
data SValue = SNum Int | SBool Bool | SPrim ArithOp | Unit | Proc [String] [Exp]
    deriving (Show, Eq)

data Exp = Apply Exp [Exp] | Cond Exp Exp Exp | Equiv Exp Exp | Begin [Exp]
    | Val SValue | Display Exp | SIdentifier String | Lambda [String] [Exp]
    deriving (Show, Eq)

delimitsNext [] = True
delimitsNext (x:_) = elem x ['(', ')', '[', ']', '"', ';', '#'] || isSpace x

lexSymb ('(':xs) = Just (xs, Open)
lexSymb (')':xs) = Just (xs, Close)
lexSymb ('[':xs) = Nothing
lexSymb (']':xs) = Nothing
lexSymb ('"':xs) = Nothing
lexSymb ('#':xs) = Nothing
lexSymb (';':xs) = Nothing
lexSymb ('+':xs) = Just (xs, Value $ SPrim Plus)
lexSymb ('-':xs) = Just (xs, Value $ SPrim Minus)
lexSymb ('*':xs) = Just (xs, Value $ SPrim Multiply)
lexSymb _ = Nothing

lexBool ('#':x:xs)
    | toLower x == 'f' && delimitsNext xs = Just (xs, Value $ SBool False)
    | toLower x == 't' && delimitsNext xs = Just (xs, Value $ SBool True)
    | otherwise = Nothing
lexBool _ = Nothing

lexIdentifier (x:xs) = if delimitsNext xs then Just (xs, [x])
    else ((x:) <$>) <$> lexIdentifier xs

lexNum acc (x:xs) = if ord '0' <= ord x && ord x <= ord '9'
    then (if delimitsNext xs then Just . (xs,) . Value . SNum else flip lexNum xs) $ acc * 10 + (ord x - ord '0')
    else Nothing
lexNum _ _ = Nothing

schlex acc [] = Right acc
schlex acc ls@(x:xs) = if isSpace x then schlex acc xs
    else uncurry (schlex . (:acc)) . swap =<< maybeToEither ("Failed to parse at character " <> [x]) (foldl (<|>) Nothing $ map ($ ls) [
        lexSymb,
        lexBool,
        lexNum 0,
        ((Identifier <$>) <$>) . lexIdentifier
    ])

parse [] p [] = Right p
parse _ _ [] = Left "Too many close brackets"
parse q p (Close:xs) = parse (ExpList p:q) [] xs
parse (ExpList q':q) p (Open:xs) = parse q (ExpList p:q') xs
parse _ _ (Open:_) = Left "Too many open brackets"
parse q p (Value v:xs) = parse q (Const v:p) xs
parse q p (Identifier i:xs) = parse q (Symbol i:p) xs

toAst (Const v) = Right $ Val v
toAst (Symbol x) = Right $ SIdentifier x
toAst (ExpList []) = Left "Empty S expression"
toAst (ExpList [Symbol "if", c, x, y]) = Cond <$> toAst c <*> toAst x <*> toAst y
toAst (ExpList (Symbol "if":_)) = Left "Wrong number of arguments to if"
toAst (ExpList [Symbol "eq?", x, y]) = Equiv <$> toAst x <*> toAst y
toAst (ExpList [Symbol "begin"]) = Left "Wrong number of arguments to begin"
toAst (ExpList (Symbol "begin":xs)) = Begin <$> mapM toAst xs
toAst (ExpList [Symbol "display", x]) = Display <$> toAst x
toAst (ExpList (Symbol "display":_)) = Left "Wrong number of arguments to display"
toAst (ExpList xs) = liftM2 Apply head tail <$> mapM toAst xs
