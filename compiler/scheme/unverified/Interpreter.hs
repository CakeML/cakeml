module Interpreter where
import Scheme
import Control.Monad (liftM2, (<=<))
import System.IO (hPutStrLn, stderr)

strict (Apply (AstPrim Plus) [AstConst (NumE x), AstConst (NumE y)]) = Right $ AstConst $ NumE $ x + y
strict (Apply (AstPrim Plus) _) = Left "Invalid arguments to +"
strict (Apply (AstPrim Multiply) [AstConst (NumE x), AstConst (NumE y)]) = Right $ AstConst $ NumE $ x * y
strict (Apply (AstPrim Multiply) _) = Left "Invalid arguments to *"

evaluate (Apply fn xs) = strict =<< liftM2 Apply (evaluate fn) (mapM evaluate xs)
evaluate x = Right x

main = either (hPutStrLn stderr) (print . head) . (mapM evaluate <=< mapM toAst <=< parse [] [] <=< flip schlex []) =<< getContents
