module Scheme where
import Data.Typeable (cast)
import Data.Char (ord, isSpace)
import Data.Maybe (fromMaybe)
import Control.Monad ((<=<), liftM2)

data ArithOp = Plus | Minus | Multiply
    deriving Show
data Token = Open | Close | NumT Int | Arith ArithOp
    deriving Show

data Exp = ExpList [Exp] | Const Value | Prim ArithOp
    deriving Show
data Value = NumE Int
    deriving Show

data AstExp = Apply AstExp [AstExp] | AstConst Value | AstPrim ArithOp
    deriving Show

lexNum (x:xs) acc = if ord '0' <= ord x && ord x <= ord '9'
    then let next = acc * 10 + (ord x - ord '0') in Just . fromMaybe next <$> lexNum xs next
    else (x:xs, Nothing)

schlex [] acc = Right acc
schlex ls acc = numOrNot $ lexNum ls 0 where
    numOrNot (rs, Just n) = schlex rs $ NumT n:acc
    numOrNot (x:xs, Nothing) = if isSpace x
        then schlex xs acc
        else symb x >>= schlex xs . (:acc)

    symb '(' = Right Open
    symb ')' = Right Close
    symb '+' = Right $ Arith Plus
    symb '-' = Right $ Arith Minus
    symb '*' = Right $ Arith Multiply
    symb c = Left $ "Invalid symbol " <> return c

--parse (Close:xs) q =
parse [] p [] = Right p
parse _ _ [] = Left "Too many close brackets"
parse q p (Close:xs) = parse (ExpList p:q) [] xs
parse (ExpList q':q) p (Open:xs) = parse q (ExpList p:q') xs
parse _ _ (Open:_) = Left "Too many open brackets"
parse q p (NumT i:xs) = parse q (Const (NumE i):p) xs
parse q p (Arith o:xs) = parse q (Prim o:p) xs

toAst (Const v) = Right $ AstConst v
toAst (Prim o) = Right $ AstPrim o
toAst (ExpList []) = Left "Empty S expression"
toAst (ExpList xs) = liftM2 Apply head tail <$> mapM toAst xs
