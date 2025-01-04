module Interpreter where
import Scheme
import Control.Monad (liftM2, (<=<), foldM, liftM3)
import System.IO (hPutStrLn, stderr)
import Data.Bool (bool)

strict:: Exp -> IO Exp
strict (Apply (PrimExp Plus) xs) = ConstExp . SNum <$> foldM add 0 xs where
    add n (ConstExp (SNum x)) = return $ n + x
    add _ _ = fail "Argument to + must be a number"
strict (Apply (PrimExp Multiply) xs) = ConstExp . SNum <$> foldM multiply 1 xs where
    multiply n (ConstExp (SNum x)) = return $ n * x
    multiply _ _ = fail "Argument to * must be a number"

evaluate :: Exp -> IO Exp
evaluate (Apply fn xs) = strict =<< liftM2 Apply (evaluate fn) (mapM evaluate xs)
evaluate (Cond c x y) = evaluate . bool y x . (ConstExp (SBool False) /=) =<< evaluate c
evaluate (Equiv x y) = ConstExp . SBool <$> ((==) <$> evaluate x <*> evaluate y)
evaluate (Begin xs) = foldM (const evaluate) Unit xs
evaluate (Display x) = (print =<< evaluate x) >> return Unit
evaluate x = return x

main = (either fail (evaluate . head) . (mapM toAst <=< parse [] [] <=< schlex [])) =<< getContents
