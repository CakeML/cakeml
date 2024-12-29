module Compiler where
import Scheme
import Prettyprinter (Pretty(pretty), (<+>), lparen, rparen)
import System.IO (hPutStrLn, stderr)
import Control.Monad ((<=<))

compile (Apply (AstPrim Plus) [x, y]) = do
    left <- compile x
    right <- compile y
    return $ lparen <> left <+> pretty '+' <+> right <> rparen
compile (Apply (AstPrim Plus) _) = Left "Invalid arguments to +"

compile (Apply (AstPrim Multiply) [x, y]) = do
    left <- compile x
    right <- compile y
    return $ lparen <> left <+> pretty '*' <+> right <> rparen
compile (Apply (AstPrim Multiply) _) = Left "Invalid arguments to *"

compile (AstConst (NumE x)) = Right $ pretty x

main = either (hPutStrLn stderr) (print . head) . (mapM compile <=< mapM toAst <=< parse [] [] <=< flip schlex []) =<< getContents
