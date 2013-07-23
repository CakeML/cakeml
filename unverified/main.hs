module Main where
import Data.List as List
import Text.Parsec as Parsec
import System.Environment (getArgs)
import Lex (lex_until_toplevel_semicolon)
import Parse (parseTop)
import Ast (elab_top)
import Ast as Ast
import Typecheck (inferTop, TenvM, TenvC, Tenv)
import Text.Parsec.Pos (initialPos)

data Error = 
    LexError String
  | ParseError String
  | TypeError String

getLexError :: Either Parsec.ParseError a -> Either Main.Error a
getLexError (Left e) = Left (LexError (show e))
getLexError (Right e) = Right e

getParseError :: Either Parsec.ParseError a -> Either Main.Error a
getParseError (Left e) = Left (ParseError (show e))
getParseError (Right e) = Right e

getTypeError :: Either String x -> Either Main.Error x
getTypeError (Left e) = Left (TypeError e)
getTypeError (Right e) = Right e

runFile :: SourcePos -> Ast.Tdef_env -> Ast.Ctor_env -> (TenvM,TenvC,Tenv) -> String -> Either Main.Error ()
runFile pos tdef_env ctor_env tenvs [] = return ()
runFile pos tdef_env ctor_env tenvs input =
  do (toks,rest,pos') <- getLexError (lex_until_toplevel_semicolon input pos);
     ast <- getParseError (parseTop toks);
     let (tdef_env', ctor_env', ast') = elab_top tdef_env ctor_env ast;
     tenvs' <- getTypeError (inferTop tenvs ast');
     runFile pos' tdef_env' ctor_env' tenvs' rest

getOut :: Either Main.Error x -> String
getOut (Left (LexError s)) = "<lex error>" ++ s
getOut (Left (ParseError s)) = "<parse error>: " ++ s
getOut (Left (TypeError s)) = "<type error>: " ++ s
getOut (Right x) = "<no error>"

main = 
  do args <- getArgs;
     let name = List.head args;
     input <- readFile name;
     -- TODO: initial envs
     let res = runFile (initialPos name) Ast.emp Ast.emp (Ast.emp,Ast.emp,Ast.emp) input;
     putStrLn (getOut res);
     return ()
