module Main where
import Data.List as List
import Text.Parsec as Parsec
import System.Environment (getArgs)
import Lex (lex_until_toplevel_semicolon)
import Parse (parseTop)
import Ast (elab_top, init_elab_env)
import Ast as Ast
import Typecheck (inferTop, TenvM, TenvC, Tenv, init_type_env)
import Text.Parsec.Pos (initialPos)
import Data.Char (isSpace)

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

getTypeError :: Either (SourcePos,String) x -> Either Main.Error x
getTypeError (Left (pos,e)) = Left (TypeError (show pos ++ "\n" ++ e))
getTypeError (Right e) = Right e

inferMerge (x',y',z') (x,y,z) =
  (merge x' x, merge y' y, merge z' z)

runFile :: SourcePos -> Ast.Tdef_env -> Ast.Ctor_env -> (TenvM,TenvC,Tenv) -> String -> Either Main.Error ()
runFile pos tdef_env ctor_env tenvs input =
  if List.all isSpace input then
    return ()
  else
    do (toks,rest,pos') <- getLexError (lex_until_toplevel_semicolon input pos);
       ast <- getParseError (parseTop toks);
       let (tdef_env', ctor_env', ast') = elab_top tdef_env ctor_env ast;
       tenvs' <- getTypeError (inferTop tenvs ast');
       runFile pos' (merge tdef_env' tdef_env) (merge ctor_env' ctor_env) (inferMerge tenvs' tenvs) rest

getOut :: Either Main.Error x -> String
getOut (Left (LexError s)) = "<lex error>\n" ++ s
getOut (Left (ParseError s)) = "<parse error>\n" ++ s
getOut (Left (TypeError s)) = "<type error>\n" ++ s
getOut (Right x) = "<no error>"

main = 
  do args <- getArgs;
     let name = List.head args;
     input <- readFile name;
     let res = runFile (initialPos name) init_elab_env Ast.emp (Ast.emp,Ast.emp,init_type_env) input;
     putStrLn (getOut res);
     return ()
