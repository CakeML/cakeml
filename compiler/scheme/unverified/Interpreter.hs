module Interpreter where
import Scheme
import Control.Monad (liftM2, (<=<), foldM, liftM3)
import System.IO (hPutStrLn, stderr)
import Data.Bool (bool)
import Data.Map.Strict (Map, empty, (!?), singleton, union, fromList)

strict :: Map String SValue -> SValue -> [SValue] -> IO SValue
strict store (Proc params exps) xs = if length params == length xs
    then last <$> mapM (evaluate $ union (fromList $ zip params xs) store) exps
    else fail "Wrong number of arguments"
strict _ (SPrim Plus) xs = SNum <$> foldM add 0 xs where
    add n (SNum x) = return $ n + x
    add _ _ = fail "Argument to + must be a number"
strict _ (SPrim Multiply) xs = SNum <$> foldM multiply 1 xs where
    multiply n (SNum x) = return $ n * x
    multiply _ _ = fail "Argument to * must be a number"

evaluate :: Map String SValue -> Exp -> IO SValue
evaluate store (Apply fn xs) = (mapM (evaluate store) xs >>=) . strict store =<< evaluate store fn
evaluate store (Cond c x y) = evaluate store . bool y x . (SBool False /=) =<< evaluate store c
evaluate store (Equiv x y) = SBool <$> ((==) <$> evaluate store x <*> evaluate store y)
evaluate store (Begin xs) = foldM (const $ evaluate store) Unit xs
evaluate store (Display x) = (print =<< evaluate store x) >> return Unit
evaluate store (SIdentifier i) = maybe (fail $ "Symbol " <> i <> " has no definition") return $ store !? i
evaluate store (Lambda params xs) = return $ Proc params xs
evaluate store (Val v) = return v

main = (either fail (mapM $ evaluate $ singleton "x" $ Proc ["y"] [Apply (Val (SPrim Multiply)) [Val (SNum 2), SIdentifier "y"]]) . (mapM toAst <=< parse [] [] <=< schlex [])) =<< getContents
