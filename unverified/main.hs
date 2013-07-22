module Main where
import Data.List as List
import Text.Parsec as Parsec
import System.Environment (getArgs)
import Lex (lex_until_toplevel_semicolon)
import Parse (parseTop)
import Ast (elab_top)
import Ast as Ast
import Typecheck (inferTop, TenvM, TenvC, Tenv)

data Error = 
    LexError
  | ParseError String
  | TypeError String

getError :: Main.Error -> Maybe a -> Either Main.Error a
getError e Nothing = Left e
getError e (Just x) = Right x

getParseError :: Either Parsec.ParseError a -> Either Main.Error a
getParseError (Left e) = Left (ParseError (show e))
getParseError (Right e) = Right e

getTypeError :: Either String x -> Either Main.Error x
getTypeError (Left e) = Left (TypeError e)
getTypeError (Right e) = Right e

runFile :: Ast.Tdef_env -> Ast.Ctor_env -> (TenvM,TenvC,Tenv) -> String -> Either Main.Error ()
runFile tdef_env ctor_env tenvs [] = return ()
runFile tdef_env ctor_env tenvs input =
  do (toks,rest) <- getError LexError (lex_until_toplevel_semicolon input);
     ast <- getParseError (parseTop toks);
     let (tdef_env', ctor_env', ast') = elab_top tdef_env ctor_env ast;
     tenvs' <- getTypeError (inferTop tenvs ast');
     runFile tdef_env' ctor_env' tenvs' rest

getOut :: Either Main.Error x -> String
getOut (Left LexError) = "<lex error>"
getOut (Left (ParseError s)) = "<parse error>: " ++ s
getOut (Left (TypeError s)) = "<type error>: " ++ s
getOut (Right x) = "<no error>"

main = 
  do args <- getArgs;
     input <- readFile (List.head args);
     -- TODO: initial envs
     let res = runFile Ast.emp Ast.emp (Ast.emp,Ast.emp,Ast.emp) input;
     putStrLn (getOut res);
     return ()
